/*
 *  Unix SMB/CIFS implementation.
 *  A dumping ground for FreeBSD-specific VFS functions. For testing case
 *  of reducing number enabled VFS modules to bare minimum by creating
 *  single large VFS module.
 * 
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, see <http://www.gnu.org/licenses/>.
 */

#include "includes.h"
#include "MacExtensions.h"
#include "smbd/smbd.h"
#include "libcli/security/security.h"
#include "nfs4_acls.h"
#include "system/filesys.h"
#include <fstab.h>
#include <sys/types.h>
#include <ufs/ufs/quota.h>

#if HAVE_FREEBSD_SUNACL_H
#include "sunacl.h"
#endif

#if HAVE_LIBZFS
#include "lib/util/tevent_ntstatus.h"
#include "modules/smb_libzfs.h"
#endif
#include <libutil.h>

#define ZFSACL_MODULE_NAME "ixnas"
static int vfs_ixnas_debug_level = DBGC_VFS;

#undef DBGC_CLASS
#define DBGC_CLASS vfs_ixnas_debug_level

struct ixnas_config_data {
	struct smbacl4_vfs_params nfs4_params;
	bool posix_rename;
	bool dosmode_enabled;
	bool dosmode_remote_storage;
	bool zfs_acl_enabled;
	bool zfs_acl_expose_snapdir;
	bool zfs_acl_denymissingspecial;
	bool zfs_space_enabled;
	bool zfs_quota_enabled;
	bool zfs_auto_homedir;
	const char *homedir_quota;
	uint64_t base_user_quota; 
};

static uint32_t ixnas_fs_capabilities(struct vfs_handle_struct *handle,
				enum timestamp_set_resolution *p_ts_res)
{
	uint32_t fs_capabilities = SMB_VFS_NEXT_FS_CAPABILITIES(handle, p_ts_res);
	struct ixnas_config_data *config;

	SMB_VFS_HANDLE_GET_DATA(handle, config,
				struct ixnas_config_data,
				return -1);

	if (config->dosmode_remote_storage) {
		fs_capabilities |= FILE_SUPPORTS_REMOTE_STORAGE;
	}
	
	return fs_capabilities;
}

/********************************************************************
 Fuctions to store DOS attributes as File Flags.
********************************************************************/
static uint32_t fileflags_to_dosmode(uint32_t fileflags)
{
	uint32_t dosmode = 0;
	if (fileflags & UF_READONLY){
		dosmode |= FILE_ATTRIBUTE_READONLY;
	}
	if (fileflags & UF_ARCHIVE){
		dosmode |= FILE_ATTRIBUTE_ARCHIVE;
	}
	if (fileflags & UF_SYSTEM){
		dosmode |= FILE_ATTRIBUTE_SYSTEM;
	}
	if (fileflags & UF_HIDDEN){
		dosmode |= FILE_ATTRIBUTE_HIDDEN;
	}
	if (fileflags & UF_SPARSE){
		dosmode |= FILE_ATTRIBUTE_SPARSE;
	}
	if (fileflags & UF_OFFLINE){
		dosmode |= FILE_ATTRIBUTE_OFFLINE;
	}

	return dosmode;
}

static uint32_t dosmode_to_fileflags(uint32_t dosmode)
{
	uint32_t fileflags = 0;
	if (dosmode & FILE_ATTRIBUTE_ARCHIVE) {
		fileflags |= UF_ARCHIVE;
	}
	if (dosmode & FILE_ATTRIBUTE_HIDDEN) {
		fileflags |= UF_HIDDEN;
	}
	if (dosmode & FILE_ATTRIBUTE_OFFLINE) {
		fileflags |= UF_OFFLINE;
	}
	if (dosmode & FILE_ATTRIBUTE_READONLY) {
		fileflags |= UF_READONLY;
	}
	if (dosmode & FILE_ATTRIBUTE_SYSTEM) {
		fileflags |= UF_SYSTEM;
	}

	return fileflags;
}

static NTSTATUS set_dos_attributes_common(struct vfs_handle_struct *handle,
					 const struct smb_filename *smb_fname,
					 uint32_t dosmode)
{
	int ret;
	bool set_dosmode_ok = false;
	NTSTATUS status = NT_STATUS_OK;
	uint32_t fileflags = dosmode_to_fileflags(dosmode);

	DBG_INFO("ixnas:set_dos_attributes: set attribute 0x%x, on file %s\n",
		dosmode, smb_fname->base_name);
	/*
	* Optimization. This is most likely set by file owner. First try without
	* performing additional permissions checks and using become_root().
	*/

	ret = SMB_VFS_CHFLAGS(handle->conn, smb_fname, fileflags);

	if (ret ==-1 && errno == EPERM) {
	/*
	* We want DOS semantics, i.e. allow non-owner with write permission to
	* change the bits on a file.   
	*/

		if (!CAN_WRITE(handle->conn)) {
			return NT_STATUS_ACCESS_DENIED;
		}

		status = smbd_check_access_rights(handle->conn, smb_fname, false,
						FILE_WRITE_ATTRIBUTES);
		if (NT_STATUS_IS_OK(status)) {
			set_dosmode_ok = true;
		}

		if (!set_dosmode_ok && lp_dos_filemode(SNUM(handle->conn))) {
			set_dosmode_ok = can_write_to_file(handle->conn, smb_fname);
		}

		if (!set_dosmode_ok){
			return NT_STATUS_ACCESS_DENIED;
		}

		/* becomeroot() because non-owners need to write flags */

		become_root();
		ret = SMB_VFS_CHFLAGS(handle->conn, smb_fname, fileflags);
		unbecome_root();

		if (ret == -1) {
			DBG_WARNING("Setting dosmode failed for %s: %s\n",
			smb_fname->base_name, strerror(errno));
			return map_nt_error_from_unix(errno);
		}
		return NT_STATUS_OK;
	}

	if (ret == -1) {
		DBG_WARNING("Setting dosmode failed for %s: %s\n",
			smb_fname->base_name, strerror(errno));
		return map_nt_error_from_unix(errno);
	}
	return NT_STATUS_OK;
}

static NTSTATUS ixnas_get_dos_attributes(struct vfs_handle_struct *handle,
					 struct smb_filename *smb_fname,
					 uint32_t *dosmode)
{
	struct ixnas_config_data *config;

	SMB_VFS_HANDLE_GET_DATA(handle, config,
				struct ixnas_config_data,
				return NT_STATUS_INTERNAL_ERROR);

	if (!config->dosmode_enabled) {
		DBG_INFO("ixnas: special dosmode handling disabled. passing to next VFS module");
		return SMB_VFS_NEXT_GET_DOS_ATTRIBUTES(handle, smb_fname, dosmode);
	}
	
	*dosmode = fileflags_to_dosmode(smb_fname->st.st_ex_flags);

	if (config->dosmode_remote_storage) {
		*dosmode |= FILE_ATTRIBUTE_OFFLINE;
	}

	return NT_STATUS_OK;
}

static NTSTATUS ixnas_fget_dos_attributes(struct vfs_handle_struct *handle,
                                            struct files_struct *fsp,
                                            uint32_t *dosmode)
{
	struct ixnas_config_data *config;

	SMB_VFS_HANDLE_GET_DATA(handle, config,
				struct ixnas_config_data,
				return NT_STATUS_INTERNAL_ERROR);

	if (!config->dosmode_enabled) {
		DBG_INFO("ixnas: special dosmode handling disabled. passing to next VFS module");
		return SMB_VFS_NEXT_FGET_DOS_ATTRIBUTES(handle, fsp, dosmode);
	}

        *dosmode = fileflags_to_dosmode(fsp->fsp_name->st.st_ex_flags);

	if (config->dosmode_remote_storage) {
		*dosmode |= FILE_ATTRIBUTE_OFFLINE;
	}

        return NT_STATUS_OK;
}

static NTSTATUS ixnas_set_dos_attributes(struct vfs_handle_struct *handle,
                                           const struct smb_filename *smb_fname,
                                           uint32_t dosmode)
{
	NTSTATUS ret;
	struct ixnas_config_data *config;

	SMB_VFS_HANDLE_GET_DATA(handle, config,
				struct ixnas_config_data,
				return NT_STATUS_INTERNAL_ERROR);

	if (!config->dosmode_enabled) {
		DBG_INFO("ixnas: special dosmode handling disabled. passing to next VFS module");
		return SMB_VFS_NEXT_SET_DOS_ATTRIBUTES(handle, smb_fname, dosmode);
	}

	ret = set_dos_attributes_common(handle, smb_fname, dosmode);
                
        return ret;
}

static NTSTATUS ixnas_fset_dos_attributes(struct vfs_handle_struct *handle,
                                            struct files_struct *fsp,
                                            uint32_t dosmode)
{
	NTSTATUS ret;
	struct ixnas_config_data *config;

	SMB_VFS_HANDLE_GET_DATA(handle, config,
				struct ixnas_config_data,
				return NT_STATUS_INTERNAL_ERROR);

	if (!config->dosmode_enabled) {
		DBG_INFO("ixnas: special dosmode handling disabled. passing to next VFS module");
		return SMB_VFS_NEXT_FSET_DOS_ATTRIBUTES(handle, fsp, dosmode);
	}
	ret = set_dos_attributes_common(handle, fsp->fsp_name, dosmode);

	return ret;
}

/********************************************************************
 Correctly calculate free space on ZFS 
 Per MS-FSCC, behavior for Windows 2000 -> 2008R2 is to account for
 user quotas in TotalAllocationUnits and CallerAvailableAllocationUnits  
 in FileFsFullSizeInformation.
********************************************************************/
#if HAVE_LIBZFS
static uint64_t ixnas_disk_free(vfs_handle_struct *handle, const struct smb_filename *smb_fname,
				uint64_t *bsize, uint64_t *dfree, uint64_t *dsize)
{
	uint64_t res;
	char rp[PATH_MAX] = { 0 };

	if (realpath(smb_fname->base_name, rp) == NULL)
		return (-1);

	DBG_DEBUG("realpath = %s\n", rp);

	res = smb_zfs_disk_free(rp, bsize, dfree, dsize, geteuid());
	if (res == (uint64_t)-1)
		res = SMB_VFS_NEXT_DISK_FREE(handle, smb_fname, bsize, dfree, dsize);
	if (res == (uint64_t)-1)
		return (res);

	DBG_DEBUG("*bsize = %" PRIu64 "\n", *bsize);
	DBG_DEBUG("*dfree = %" PRIu64 "\n", *dfree);
	DBG_DEBUG("*dsize = %" PRIu64 "\n", *dsize);

	return (res);
}
#endif

/********************************************************************
 Functions for OSX compatibility. 
********************************************************************/
static NTSTATUS ixnas_create_file(vfs_handle_struct *handle,
				  struct smb_request *req,
				  uint16_t root_dir_fid,
				  struct smb_filename *smb_fname,
				  uint32_t access_mask,
				  uint32_t share_access,
				  uint32_t create_disposition,
				  uint32_t create_options,
				  uint32_t file_attributes,
				  uint32_t oplock_request,
				  struct smb2_lease *lease,
				  uint64_t allocation_size,
				  uint32_t private_flags,
				  struct security_descriptor *sd,
				  struct ea_list *ea_list,
				  files_struct **result,
				  int *pinfo,
				  const struct smb2_create_blobs *in_context_blobs,
				  struct smb2_create_blobs *out_context_blobs)
{
	NTSTATUS status;
	struct ixnas_config_data *config = NULL;
	files_struct *fsp = NULL;

	SMB_VFS_HANDLE_GET_DATA(handle, config,
				struct ixnas_config_data,
				return NT_STATUS_INTERNAL_ERROR);

	status = SMB_VFS_NEXT_CREATE_FILE(
		handle, req, root_dir_fid, smb_fname,
		access_mask, share_access,
		create_disposition, create_options,
		file_attributes, oplock_request,
		lease,
		allocation_size, private_flags,
		sd, ea_list, result,
		pinfo, in_context_blobs, out_context_blobs);

	if (!NT_STATUS_IS_OK(status)) {
		return status;
	}

	fsp = *result;

	if (config->posix_rename && fsp->is_directory) {
		fsp->posix_flags |= FSP_POSIX_FLAGS_RENAME;
	}

	return status;
}

/********************************************************************
 Functions to use ZFS ACLs. 
********************************************************************/
/* zfs_get_nt_acl()
 * read the local file's acls and return it in NT form
 * using the NFSv4 format conversion
 */
static NTSTATUS zfs_get_nt_acl_common(struct connection_struct *conn,
				      TALLOC_CTX *mem_ctx,
				      const struct smb_filename *smb_fname,
				      struct SMB4ACL_T **ppacl,
				      struct ixnas_config_data *config)
{
	int naces, i;
	ace_t *acebuf;
	struct SMB4ACL_T *pacl;
	SMB_STRUCT_STAT sbuf;
	const SMB_STRUCT_STAT *psbuf = NULL;
	int ret;
	bool is_dir;
	bool inherited_present = false;

	if (VALID_STAT(smb_fname->st)) {
		psbuf = &smb_fname->st;
	}

	if (psbuf == NULL) {
		ret = vfs_stat_smb_basename(conn, smb_fname, &sbuf);
		if (ret != 0) {
			DBG_INFO("stat [%s]failed: %s\n",
				 smb_fname_str_dbg(smb_fname), strerror(errno));
			return map_nt_error_from_unix(errno);
		}
		psbuf = &sbuf;
	}
	is_dir = S_ISDIR(psbuf->st_ex_mode);

	/* read the number of file aces */
	if((naces = acl(smb_fname->base_name, ACE_GETACLCNT, 0, NULL)) == -1) {
		if(errno == ENOSYS) {
			DBG_ERR("acl(ACE_GETACLCNT, %s): Operation is not "
				  "supported on the filesystem where the file "
				  "reside\n", smb_fname->base_name);
		} else {
			DBG_ERR("acl(ACE_GETACLCNT, %s): %s ", smb_fname->base_name,
					strerror(errno));
		}
		return map_nt_error_from_unix(errno);
	}
	/* allocate the field of ZFS aces */
	mem_ctx = talloc_tos();
	acebuf = (ace_t *) talloc_size(mem_ctx, sizeof(ace_t)*naces);
	if(acebuf == NULL) {
		return NT_STATUS_NO_MEMORY;
	}
	/* read the aces into the field */
	if(acl(smb_fname->base_name, ACE_GETACL, naces, acebuf) < 0) {
		DBG_ERR("acl(ACE_GETACL, %s): %s ", smb_fname->base_name,
				strerror(errno));
		return map_nt_error_from_unix(errno);
	}
	/* create SMB4ACL data */
	if((pacl = smb_create_smb4acl(mem_ctx)) == NULL) {
		return NT_STATUS_NO_MEMORY;
	}
	for(i=0; i<naces; i++) {
		SMB_ACE4PROP_T aceprop;

		aceprop.aceType  = (uint32_t) acebuf[i].a_type;
		aceprop.aceFlags = (uint32_t) acebuf[i].a_flags;
		aceprop.aceMask  = (uint32_t) acebuf[i].a_access_mask;
		aceprop.who.id   = (uint32_t) acebuf[i].a_who;

		if (aceprop.aceFlags & ACE_EVERYONE){
			if (!(acebuf[i].a_access_mask &= ACE_ALL_PERMS)) {
				continue;
			}
		}

		/*
		 * Windows clients expect SYNC on acls to correctly allow
		 * rename, cf bug #7909. But not on DENY ace entries, cf bug
		 * #8442.
		 */
		if (aceprop.aceType == SMB_ACE4_ACCESS_ALLOWED_ACE_TYPE) {
			aceprop.aceMask |= SMB_ACE4_SYNCHRONIZE;
		}

		if (is_dir && (aceprop.aceMask & SMB_ACE4_ADD_FILE)) {
			aceprop.aceMask |= SMB_ACE4_DELETE_CHILD;
		}
 		/*
		 * Test whether ACL contains any ACEs with the
		 * inherited flag set. We use this to determine whether
   		 * to set DACL_PROTECTED in the security descriptor.
   		 */
 		if(aceprop.aceFlags & ACE_INHERITED_ACE) {
 			inherited_present = true;
 		}

		if(aceprop.aceFlags & ACE_OWNER) {
			aceprop.flags = SMB_ACE4_ID_SPECIAL;
			aceprop.who.special_id = SMB_ACE4_WHO_OWNER;
		} else if(aceprop.aceFlags & ACE_GROUP) {
			aceprop.flags = SMB_ACE4_ID_SPECIAL;
			aceprop.who.special_id = SMB_ACE4_WHO_GROUP;
		} else if(aceprop.aceFlags & ACE_EVERYONE) {
			aceprop.flags = SMB_ACE4_ID_SPECIAL;
			aceprop.who.special_id = SMB_ACE4_WHO_EVERYONE;
		} else {
			aceprop.flags	= 0;
		}
		if(smb_add_ace4(pacl, &aceprop) == NULL)
			return NT_STATUS_NO_MEMORY;
	}

	/*
  	 * If the ACL doesn't contain any inherited ACEs, then set DACL_PROTECTED 
  	 * in the security descriptor using smb4acl4_set_control_flags().
   	 * This makes it so that the "Disable Inheritance" button works in Windows Explorer
   	 * and prevents resulting ACL from auto-inheriting ACL changes in parent directory.
   	 */
 	if (!inherited_present) {
 		smbacl4_set_controlflags(pacl, SEC_DESC_DACL_PROTECTED|SEC_DESC_SELF_RELATIVE);
 	}

	*ppacl = pacl;
	return NT_STATUS_OK;
}

/* call-back function processing the NT acl -> ZFS acl using NFSv4 conv. */
static bool zfs_process_smbacl(vfs_handle_struct *handle, files_struct *fsp,
			       struct SMB4ACL_T *smbacl)
{
	SMB_ACE4PROP_T hidden_ace;
	if (S_ISDIR(fsp->fsp_name->st.st_ex_mode)) {
		hidden_ace.flags = SMB_ACE4_ID_SPECIAL;
		hidden_ace.who.id = SMB_ACE4_WHO_EVERYONE;
		hidden_ace.aceType = SMB_ACE4_ACCESS_ALLOWED_ACE_TYPE;
		hidden_ace.aceFlags = (SMB_ACE4_FILE_INHERIT_ACE|SMB_ACE4_DIRECTORY_INHERIT_ACE);
		hidden_ace.aceMask = 0;
		DBG_DEBUG("ixnas: setting empty everyone@ ace on dir  %s \n", fsp->fsp_name->base_name);	
	} else {
		hidden_ace.flags = SMB_ACE4_ID_SPECIAL;
		hidden_ace.who.id = SMB_ACE4_WHO_EVERYONE;
		hidden_ace.aceType = SMB_ACE4_ACCESS_ALLOWED_ACE_TYPE;
		hidden_ace.aceFlags = 0;
		hidden_ace.aceMask = 0;
		DBG_DEBUG("ixnas: setting empty everyone@ ace on file  %s \n", fsp->fsp_name->base_name);	
	}

	smb_add_ace4(smbacl, &hidden_ace);

	int naces = smb_get_naces(smbacl), i;
	ace_t *acebuf;
	struct SMB4ACE_T *smbace;
	TALLOC_CTX	*mem_ctx;
	bool have_special_id = false;

	/* allocate the field of ZFS aces */
	mem_ctx = talloc_tos();
	acebuf = (ace_t *) talloc_size(mem_ctx, sizeof(ace_t)*naces);
	if(acebuf == NULL) {
		errno = ENOMEM;
		return False;
	}
	/* handle all aces */
	for(smbace = smb_first_ace4(smbacl), i = 0;
			smbace!=NULL;
			smbace = smb_next_ace4(smbace), i++) {
		SMB_ACE4PROP_T *aceprop = smb_get_ace4(smbace);

		acebuf[i].a_type        = aceprop->aceType;
		acebuf[i].a_flags       = aceprop->aceFlags;
		acebuf[i].a_access_mask = aceprop->aceMask;
		/* SYNC on acls is a no-op on ZFS.
		   See bug #7909. */
		acebuf[i].a_access_mask &= ~SMB_ACE4_SYNCHRONIZE;
		acebuf[i].a_who         = aceprop->who.id;
		if(aceprop->flags & SMB_ACE4_ID_SPECIAL) {
			switch(aceprop->who.special_id) {
			case SMB_ACE4_WHO_EVERYONE:
				acebuf[i].a_flags |= ACE_EVERYONE;
				break;
			case SMB_ACE4_WHO_OWNER:
				acebuf[i].a_flags |= ACE_OWNER;
				break;
			case SMB_ACE4_WHO_GROUP:
				acebuf[i].a_flags |= ACE_GROUP|ACE_IDENTIFIER_GROUP;
				break;
			default:
				DBG_INFO("unsupported special_id %d\n", \
					aceprop->who.special_id);
				continue; /* don't add it !!! */
			}
			have_special_id = true;
		}
	}

	if (!have_special_id
	    && lp_parm_bool(fsp->conn->params->service, "ixnas",
			    "denymissingspecial", false)) {
		errno = EACCES;
		return false;
	}

	SMB_ASSERT(i == naces);

	/* store acl */
	if(acl(fsp->fsp_name->base_name, ACE_SETACL, naces, acebuf)) {
		if(errno == ENOSYS) {
			DBG_ERR("acl(ACE_SETACL, %s): Operation is not "
				  "supported on the filesystem where the file "
				  "reside", fsp_str_dbg(fsp));
		} else {
			DBG_DEBUG("acl(ACE_SETACL, %s): %s ", fsp_str_dbg(fsp),
				  strerror(errno));
		}
		return 0;
	}

	return True;
}

/* zfs_set_nt_acl()
 * set the local file's acls obtaining it in NT form
 * using the NFSv4 format conversion
 */
static NTSTATUS zfs_set_nt_acl(vfs_handle_struct *handle, files_struct *fsp,
			   uint32_t security_info_sent,
			   const struct security_descriptor *psd,
			   struct ixnas_config_data *config)
{
        return smb_set_nt_acl_nfs4(handle, fsp, &config->nfs4_params, security_info_sent, psd,
				   zfs_process_smbacl);
}

static NTSTATUS ixnas_fget_nt_acl(struct vfs_handle_struct *handle,
				   struct files_struct *fsp,
				   uint32_t security_info,
				   TALLOC_CTX *mem_ctx,
				   struct security_descriptor **ppdesc)
{
	struct SMB4ACL_T *pacl;
	NTSTATUS status;
	TALLOC_CTX *frame = talloc_stackframe();
	struct ixnas_config_data *config;

	SMB_VFS_HANDLE_GET_DATA(handle, config,
				struct ixnas_config_data,
				return NT_STATUS_INTERNAL_ERROR);

	if (!config->zfs_acl_enabled) {
		TALLOC_FREE(frame);
		return SMB_VFS_NEXT_FGET_NT_ACL(handle, fsp, security_info, mem_ctx, ppdesc);
	}

	status = zfs_get_nt_acl_common(handle->conn, frame,
				       fsp->fsp_name, &pacl, config);

	if (!NT_STATUS_IS_OK(status)) {
		TALLOC_FREE(frame);
		// Control whether we expose .zfs/snapdir over SMB.
		if (!config->zfs_acl_expose_snapdir || !NT_STATUS_EQUAL(status, NT_STATUS_NOT_SUPPORTED)) {
			return status;
		}

		status = make_default_filesystem_acl(mem_ctx,
						     DEFAULT_ACL_POSIX,
						     fsp->fsp_name->base_name,
						     &fsp->fsp_name->st,
						     ppdesc);
		if (!NT_STATUS_IS_OK(status)) {
			return status;
		}
		(*ppdesc)->type |= SEC_DESC_DACL_PROTECTED;
		return NT_STATUS_OK;
	}

	status = smb_fget_nt_acl_nfs4(fsp, &config->nfs4_params, security_info, mem_ctx,
				      ppdesc, pacl);
	TALLOC_FREE(frame);
	return status;
}

static NTSTATUS ixnas_get_nt_acl(struct vfs_handle_struct *handle,
				const struct smb_filename *smb_fname,
				uint32_t security_info,
				TALLOC_CTX *mem_ctx,
				struct security_descriptor **ppdesc)
{
	struct SMB4ACL_T *pacl;
	NTSTATUS status;
	TALLOC_CTX *frame = talloc_stackframe();
	struct ixnas_config_data *config;

	SMB_VFS_HANDLE_GET_DATA(handle, config,
				struct ixnas_config_data,
				return NT_STATUS_INTERNAL_ERROR);

	if (!config->zfs_acl_enabled) {
		TALLOC_FREE(frame);
		return SMB_VFS_NEXT_GET_NT_ACL(handle, smb_fname, security_info, mem_ctx, ppdesc);
	}

	status = zfs_get_nt_acl_common(handle->conn, frame, smb_fname, &pacl, config);

	if (!NT_STATUS_IS_OK(status)) {
		TALLOC_FREE(frame);
		// Control whether we expose .zfs/snapdir over SMB.
		if (!config->zfs_acl_expose_snapdir || !NT_STATUS_EQUAL(status, NT_STATUS_NOT_SUPPORTED)) {
			return status;
		}

		if (!VALID_STAT(smb_fname->st)) {
			DBG_ERR("No stat info for [%s]\n",
				smb_fname_str_dbg(smb_fname));
			return NT_STATUS_INTERNAL_ERROR;
		}

		status = make_default_filesystem_acl(mem_ctx,
						     DEFAULT_ACL_POSIX,
						     smb_fname->base_name,
						     &smb_fname->st,
						     ppdesc);
		if (!NT_STATUS_IS_OK(status)) {
			return status;
		}
		(*ppdesc)->type |= SEC_DESC_DACL_PROTECTED;
		return NT_STATUS_OK;
	}

	status = smb_get_nt_acl_nfs4(handle->conn,
					smb_fname,
					&config->nfs4_params,
					security_info,
					mem_ctx,
					ppdesc,
					pacl);
	TALLOC_FREE(frame);
	return status;
}

static NTSTATUS ixnas_fset_nt_acl(vfs_handle_struct *handle,
			 files_struct *fsp,
			 uint32_t security_info_sent,
			 const struct security_descriptor *psd)
{
	struct ixnas_config_data *config;

	SMB_VFS_HANDLE_GET_DATA(handle, config,
				struct ixnas_config_data,
				return NT_STATUS_INTERNAL_ERROR);

	if (!config->zfs_acl_enabled) {
		return SMB_VFS_NEXT_FSET_NT_ACL(handle, fsp, security_info_sent, psd);
	}

	return zfs_set_nt_acl(handle, fsp, security_info_sent, psd, config);
}

static SMB_ACL_T ixnas_fail__sys_acl_get_file(vfs_handle_struct *handle,
					const struct smb_filename *smb_fname,
					SMB_ACL_TYPE_T type,
					TALLOC_CTX *mem_ctx)
{
	return (SMB_ACL_T)NULL;
}

static SMB_ACL_T ixnas_fail__sys_acl_get_fd(vfs_handle_struct *handle,
					     files_struct *fsp,
					     TALLOC_CTX *mem_ctx)
{
	return (SMB_ACL_T)NULL;
}

static int ixnas_fail__sys_acl_set_file(vfs_handle_struct *handle,
					 const struct smb_filename *smb_fname,
					 SMB_ACL_TYPE_T type,
					 SMB_ACL_T theacl)
{
	return -1;
}

static int ixnas_fail__sys_acl_set_fd(vfs_handle_struct *handle,
				       files_struct *fsp,
				       SMB_ACL_T theacl)
{
	return -1;
}

static int ixnas_fail__sys_acl_delete_def_file(vfs_handle_struct *handle,
			const struct smb_filename *smb_fname)
{
	return -1;
}

static int ixnas_fail__sys_acl_blob_get_file(vfs_handle_struct *handle,
			const struct smb_filename *smb_fname,
			TALLOC_CTX *mem_ctx,
			char **blob_description,
			DATA_BLOB *blob)
{
	return -1;
}

static int ixnas_fail__sys_acl_blob_get_fd(vfs_handle_struct *handle, files_struct *fsp, TALLOC_CTX *mem_ctx, char **blob_description, DATA_BLOB *blob)
{
	return -1;
}

/********************************************************************
 Expose ZFS user/group quotas 
********************************************************************/
static int ixnas_get_quota(struct vfs_handle_struct *handle,
                                const struct smb_filename *smb_fname,
                                enum SMB_QUOTA_TYPE qtype,
                                unid_t id,
                                SMB_DISK_QUOTA *qt)
{
	int ret;
	char rp[PATH_MAX] = { 0 };
	struct ixnas_config_data *config;
	uint64_t hardlimit, usedspace;
	uid_t current_user = geteuid();
	hardlimit = usedspace = 0;

	SMB_VFS_HANDLE_GET_DATA(handle, config,
				struct ixnas_config_data,
				return -1);

	if (!config->zfs_quota_enabled) {
		DBG_DEBUG("Quotas disabled in ixnas configuration.\n");
		errno = ENOSYS;
		return -1;
	}

	if (realpath(smb_fname->base_name, rp) == NULL) {
		DBG_ERR("failed to get realpath for (%s)\n", smb_fname->base_name);
		return (-1);
	}
	switch (qtype) {
	case SMB_USER_QUOTA_TYPE:
	case SMB_USER_FS_QUOTA_TYPE:
		//passing -1 to quotactl means that the current UID should be used. Do the same.
		if (id.uid == -1) {
			become_root();
       			ret = smb_zfs_get_quota(rp, current_user, qtype, &hardlimit, &usedspace);
			unbecome_root();
		}
		else {
			become_root();
       			ret = smb_zfs_get_quota(rp, id.uid, qtype, &hardlimit, &usedspace);
			unbecome_root();
		}
		break;
	case SMB_GROUP_QUOTA_TYPE:
	case SMB_GROUP_FS_QUOTA_TYPE:
		become_root();
        	ret = smb_zfs_get_quota(rp, id.gid, qtype, &hardlimit, &usedspace);
		unbecome_root();
		break;
        default:
		DBG_ERR("Unrecognized quota type.\n");
		ret = -1;
                break;
        }

	ZERO_STRUCTP(qt);
	qt->bsize = 1024;
	qt->hardlimit = hardlimit;
	qt->softlimit = hardlimit;
	qt->curblocks = usedspace;
	qt->ihardlimit = hardlimit;
	qt->isoftlimit = hardlimit;
	qt->curinodes = usedspace;
	qt->qtype = qtype;
	qt->qflags = QUOTAS_DENY_DISK|QUOTAS_ENABLED;

        DBG_INFO("ixnas_get_quota: hardlimit: (%lu), usedspace: (%lu)\n", qt->hardlimit, qt->curblocks);

        return ret;
}

static int ixnas_set_quota(struct vfs_handle_struct *handle,
			enum SMB_QUOTA_TYPE qtype, unid_t id,
			SMB_DISK_QUOTA *qt)
{
	struct ixnas_config_data *config;
	int ret;
	

	SMB_VFS_HANDLE_GET_DATA(handle, config,
				struct ixnas_config_data,
				return -1);

	if (!config->zfs_quota_enabled) {
		DBG_DEBUG("Quotas disabled in ixnas configuration.\n");
		errno = ENOSYS;
		return -1;
	}

	become_root();
	switch (qtype) {
	case SMB_USER_QUOTA_TYPE:
	case SMB_USER_FS_QUOTA_TYPE:
		DBG_INFO("ixnas_set_quota: quota type: (%d), id: (%d), h-limit: (%lu), s-limit: (%lu)\n", 
			qtype, id.uid, qt->hardlimit, qt->softlimit);
		become_root();
		ret = smb_zfs_set_quota(handle->conn->connectpath, id.uid, qtype, qt->hardlimit);
		unbecome_root();
		break;
	case SMB_GROUP_QUOTA_TYPE:
	case SMB_GROUP_FS_QUOTA_TYPE:
		DBG_INFO("ixnas_set_quota: quota type: (%d), id: (%d), h-limit: (%lu), s-limit: (%lu)\n", 
			qtype, id.gid, qt->hardlimit, qt->softlimit);
		become_root();
		ret = smb_zfs_set_quota(handle->conn->connectpath, id.gid, qtype, qt->hardlimit);
		unbecome_root();
		break;
        default:
		DBG_ERR("Received unknown quota type.\n");
		ret = -1;
		break;
        }

	return ret;

}


/********************************************************************
 Create datasets for home directories. We fail if the path already
 exists  
********************************************************************/

static int create_zfs_autohomedir(vfs_handle_struct *handle, 
				  const char *homedir_quota,
				  const char *user)
{
	bool ret;
	int naces;
	char rp[PATH_MAX] = { 0 };
	char *parent;
	const char *base;
	ace_t *parent_acl;
	TALLOC_CTX *tmp_ctx = talloc_new(handle->data);

	if (realpath(handle->conn->connectpath, rp)) {
		DEBUG(0, ("Home directory already exists. Skipping dataset creation\n") );
		TALLOC_FREE(tmp_ctx);
		return -1;	
	}

	if (!parent_dirname(talloc_tos(), handle->conn->connectpath, &parent, &base)) {
		TALLOC_FREE(tmp_ctx);
		return -1;
	}

	DBG_INFO("Preparing to create dataset (%s) with parentdir (%s) with quota (%s)\n", 
		parent, base, homedir_quota);

	if (realpath(parent, rp) == NULL ){
		DBG_ERR("Parent directory does not exist, skipping automatic dataset creation.\n");
		TALLOC_FREE(parent);
		TALLOC_FREE(tmp_ctx);
		return -1;
	}

	ret = smb_zfs_create_homedir(parent, base, homedir_quota);

	if ((naces = acl(parent, ACE_GETACLCNT, 0, NULL)) < 0) {
		DBG_ERR("ACE_GETACLCNT failed with (%s)\n", strerror(errno));
		TALLOC_FREE(parent);
		TALLOC_FREE(tmp_ctx);
		return -1;
	}
	if ((parent_acl = talloc_size(tmp_ctx, sizeof(ace_t) * naces)) == NULL) {
		DBG_ERR("Failed to allocate memory for parent ACL\n");
		errno = ENOMEM;
		TALLOC_FREE(parent);
		TALLOC_FREE(tmp_ctx);
		return -1;
	}

	if ((acl(parent, ACE_GETACL, naces, parent_acl)) < 0) {
		DBG_ERR("ACE_GETACL failed with (%s)\n", strerror(errno));
		TALLOC_FREE(parent);
		TALLOC_FREE(tmp_ctx);
		return -1;
	}

	if (acl(handle->conn->connectpath, ACE_SETACL, naces, parent_acl) < 0) {
		DBG_ERR("ACE_SETACL failed with (%s)\n", strerror(errno));
		TALLOC_FREE(parent);
		TALLOC_FREE(tmp_ctx);
		return -1;
	}

	if (lp_parm_bool(SNUM(handle->conn), "ixnas", "chown_homedir", true)) {
		struct passwd *current_user = Get_Pwnam_alloc(tmp_ctx, user);
		if ( !current_user ) {
			DBG_ERR("Get_Pwnam_alloc failed for (%s).\n", user); 
			TALLOC_FREE(parent);
			TALLOC_FREE(tmp_ctx);
			return -1;
		}		
		if (chown(handle->conn->connectpath, current_user->pw_uid, current_user->pw_gid) < 0) {
			DBG_ERR("Failed to chown (%s) to (%u:%u)\n",
				handle->conn->connectpath, current_user->pw_uid, getegid() );
			ret = -1;
		}	
	} 

	TALLOC_FREE(parent);
	TALLOC_FREE(tmp_ctx);
        return ret;
}

/*
 * Fake the presence of a base quota. Check if user quota already exists.
 * If it exists, then we assume that the base quota has either already been set
 * or it has been modified by the admin. In either case, do nothing.
 */

static int set_base_user_quota(vfs_handle_struct *handle, uint64_t base_quota, const char *user)
{
	int ret;
	uint64_t existing_quota, usedspace;
	existing_quota = usedspace = 0;
	uid_t current_user = nametouid(user);
	base_quota /= 1024;

	if ( !current_user ) {
		DBG_ERR("Failed to convert (%s) to uid.\n", user); 
		return -1;
	}

	if ( smb_zfs_get_quota(handle->conn->connectpath, 
				current_user,
				SMB_USER_QUOTA_TYPE,
				&existing_quota,
				&usedspace) < 0 ) {
		DBG_ERR("Failed to get base quota uid: (%u), path (%s)\n",
			current_user, handle->conn->connectpath );
		return -1;
	}

	DBG_INFO("set_base_user_quote: uid (%u), quota (%lu)\n", current_user, base_quota);

	if ( !existing_quota ) {
		ret = smb_zfs_set_quota(handle->conn->connectpath,
					current_user,
					SMB_USER_QUOTA_TYPE,
					base_quota);
		if (!ret) {
			DBG_ERR("Failed to set base quota uid: (%u), path (%s), value (%lu)\n",
				current_user, handle->conn->connectpath, base_quota );
		}
	}
	return ret;
}


/********************************************************************
 Optimization. Load parameters on connect. This allows us to enable
 and disable portions of the large vfs module on demand.
********************************************************************/
static int ixnas_connect(struct vfs_handle_struct *handle,
			    const char *service, const char *user)
{
	struct ixnas_config_data *config;
	int ret;
	const char *homedir_quota = NULL;
	const char *base_quota_str = NULL;

	config = talloc_zero(handle->conn, struct ixnas_config_data);
	if (!config) {
		DEBUG(0, ("talloc_zero() failed\n"));
		errno = ENOMEM;
		return -1;
	}	

#if HAVE_LIBZFS
	/* Parameters for homedirs and quotas */
	config->zfs_auto_homedir = lp_parm_bool(SNUM(handle->conn), 
			"ixnas", "zfs_auto_homedir", false);
	config->homedir_quota = lp_parm_const_string(SNUM(handle->conn),
			"ixnas", "homedir_quota", NULL);
	
	base_quota_str = lp_parm_const_string(SNUM(handle->conn),
			"ixnas", "base_user_quota", NULL);

	if (base_quota_str != NULL) {
		config->base_user_quota = conv_str_size(base_quota_str); 
        }

	if (config->base_user_quota) {
		set_base_user_quota(handle, config->base_user_quota, user);
	}

	if (config->zfs_auto_homedir) {
		create_zfs_autohomedir(handle, config->homedir_quota, user);
	}
#endif

	/* OS-X Compatibility */
	config->posix_rename = lp_parm_bool(SNUM(handle->conn),
			"ixnas", "posix_rename", false);

	/* DOSMODE PARAMETERS */
	config->dosmode_enabled = lp_parm_bool(SNUM(handle->conn),
			"ixnas", "dosmode_enabled", true);
	/* 
	 * When DOS modes are mapped to file flags, make sure other alternate
	 * mapping of DOS modes are disabled.
	 */

	if (config->dosmode_enabled) {
		if ((lp_map_readonly(SNUM(handle->conn))) == MAP_READONLY_YES) {
			DBG_INFO("ixnas:dosmode to file flag mapping enabled,"
				  "disabling 'map readonly'\n");
			lp_do_parameter(SNUM(handle->conn), "map readonly",
					"no");
		}

		if (lp_map_archive(SNUM(handle->conn))) {
			DBG_INFO("ixnas:dosmode to file flag mapping enabled,"
				  "disabling 'map archive'\n");
			lp_do_parameter(SNUM(handle->conn), "map archive",
					"no");
		}

		if (lp_store_dos_attributes(SNUM(handle->conn))){
			DBG_INFO("ixnas:dosmode to file flag mapping enabled,"
				  "disabling 'store dos attributes'\n");
			lp_do_parameter(SNUM(handle->conn), "store dos attributes",
					"no");
		}

		/*
		 * Check to see if we want to enable offline files support. This is
		 * Optimization inspired by vfs_offline by Uri Simchoni. Improves dir
		 * listing speed for Windows Explorer by making it so that thumbnails
		 * aren't generated
		 */
		config->dosmode_remote_storage = lp_parm_bool(SNUM(handle->conn),
			"ixnas", "dosmode_remote_storage", false);
	}

	/* ZFS ACL PARAMETERS */
	config->zfs_acl_enabled = lp_parm_bool(SNUM(handle->conn),
			"ixnas", "zfs_acl_enabled", true);

	if (config->zfs_acl_enabled) {
		config->zfs_acl_expose_snapdir = lp_parm_bool(SNUM(handle->conn),
			"ixnas","zfsacl_expose_snapdir", true);	
		
		config->zfs_acl_denymissingspecial = lp_parm_bool(SNUM(handle->conn),
			"ixnas","zfsacl_denymissingspecial",false);
	}
	
	/* ZFS SPACE PARAMETERS */
#if HAVE_LIBZFS
	config->zfs_space_enabled = lp_parm_bool(SNUM(handle->conn),
			"ixnas", "zfs_space_enabled", true);

	config->zfs_quota_enabled = lp_parm_bool(SNUM(handle->conn),
			"ixnas", "zfs_quota_enabled", true);
#endif
	
	ret = SMB_VFS_NEXT_CONNECT(handle, service, user);
	if (ret < 0) {
		TALLOC_FREE(config);
		return ret;
	}

	ret = smbacl4_get_vfs_params(handle->conn, &config->nfs4_params);
	if (ret < 0) {
		TALLOC_FREE(config);
		return ret;
	}

	SMB_VFS_HANDLE_SET_DATA(handle, config,
				NULL, struct ixnas_config_data,
				return -1);

	return 0;
}

static struct vfs_fn_pointers ixnas_fns = {
	.connect_fn = ixnas_connect,
	.create_file_fn = ixnas_create_file,
	.fs_capabilities_fn = ixnas_fs_capabilities,
	/* dosmode_enabled */
	.get_dos_attributes_fn = ixnas_get_dos_attributes,
	.fget_dos_attributes_fn = ixnas_fget_dos_attributes,
	.set_dos_attributes_fn = ixnas_set_dos_attributes,
	.fset_dos_attributes_fn = ixnas_fset_dos_attributes,
	/* zfs_acl_enabled = true */
	.fget_nt_acl_fn = ixnas_fget_nt_acl,
	.get_nt_acl_fn = ixnas_get_nt_acl,
	.fset_nt_acl_fn = ixnas_fset_nt_acl,
	.sys_acl_get_file_fn = ixnas_fail__sys_acl_get_file,
	.sys_acl_get_fd_fn = ixnas_fail__sys_acl_get_fd,
	.sys_acl_blob_get_file_fn = ixnas_fail__sys_acl_blob_get_file,
	.sys_acl_blob_get_fd_fn = ixnas_fail__sys_acl_blob_get_fd,
	.sys_acl_set_file_fn = ixnas_fail__sys_acl_set_file,
	.sys_acl_set_fd_fn = ixnas_fail__sys_acl_set_fd,
	.sys_acl_delete_def_file_fn = ixnas_fail__sys_acl_delete_def_file,
	
#if HAVE_LIBZFS
	.get_quota_fn = ixnas_get_quota,
	.set_quota_fn = ixnas_set_quota,
	.disk_free_fn = ixnas_disk_free
#endif
};

NTSTATUS vfs_ixnas_init(TALLOC_CTX *);
NTSTATUS vfs_ixnas_init(TALLOC_CTX *ctx)
{
	return smb_register_vfs(SMB_VFS_INTERFACE_VERSION, "ixnas",
				&ixnas_fns);

	vfs_ixnas_debug_level = debug_add_class("ixnas");
	if (vfs_ixnas_debug_level == -1) {
		vfs_ixnas_debug_level = DBGC_VFS;
		DEBUG(0, ("%s: Couldn't register custom debugging class!\n",
			"vfs_ixnas_init"));
	} else {
		DEBUG(10, ("%s: Debug class number of '%s': %d\n",
			"vfs_ixnas_init","ixnas",vfs_ixnas_debug_level));
	}

}
