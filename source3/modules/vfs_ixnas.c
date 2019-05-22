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
#include "librpc/gen_ndr/ndr_security.h"
#include "../libcli/security/dom_sid.h"
#include "../libcli/security/security.h"
#include "passdb/lookup_sid.h"
#include "nfs4_acls.h"
#include "system/filesys.h"
#include <fstab.h>
#include <sys/types.h>
#include <ufs/ufs/quota.h>
#include <sys/acl.h>

#if HAVE_LIBZFS
#include "lib/util/tevent_ntstatus.h"
#include "modules/smb_libzfs.h"
#endif
#include <libutil.h>

#if HAVE_FREEBSD_SUNACL_H
#include "sunacl.h"
#endif

#define ZFSACL_MODULE_NAME "ixnas"
static int vfs_ixnas_debug_level = DBGC_VFS;

#undef DBGC_CLASS
#define DBGC_CLASS vfs_ixnas_debug_level

struct ixnas_config_data {
	struct smbacl4_vfs_params nfs4_params;
	bool posix_rename;
	bool zfs_acl_enabled;
	bool zfs_acl_expose_snapdir;
	bool zfs_acl_sortaces;
	bool zfs_acl_map_modify;
	bool zfs_acl_ignore_empty_mode;
	bool zfs_space_enabled;
	bool zfs_quota_enabled;
	bool zfs_auto_homedir;
	const char *homedir_quota;
	uint64_t base_user_quota; 
};
extern const struct generic_mapping file_generic_mapping;

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
	if (dosmode & FILE_ATTRIBUTE_SPARSE) {
		fileflags |= UF_SPARSE;
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
	*dosmode |= fileflags_to_dosmode(smb_fname->st.st_ex_flags);

	if (S_ISDIR(smb_fname->st.st_ex_mode)) {
	/*
 	 * Windows default behavior appears to be that the archive bit 
 	 * on a directory is only explicitly set by clients. FreeBSD
 	 * sets this bit when the directory's contents are modified. 
 	 * This is a temporary hack until we can make OS behavior 
 	 * configurable 
 	 */
		*dosmode &= ~FILE_ATTRIBUTE_ARCHIVE;
	}

	return NT_STATUS_OK;
}

static NTSTATUS ixnas_fget_dos_attributes(struct vfs_handle_struct *handle,
                                            struct files_struct *fsp,
                                            uint32_t *dosmode)
{
        *dosmode |= fileflags_to_dosmode(fsp->fsp_name->st.st_ex_flags);

	if (S_ISDIR(fsp->fsp_name->st.st_ex_mode)) {
	/*
 	 * Windows default behavior appears to be that the archive bit 
 	 * on a directory is only explicitly set by clients. FreeBSD
 	 * sets this bit when the directory's contents are modified. 
 	 * This is a temporary hack until we can make OS behavior 
 	 * configurable 
 	 */
		*dosmode &= ~FILE_ATTRIBUTE_ARCHIVE;
	}

        return NT_STATUS_OK;
}

static NTSTATUS ixnas_set_dos_attributes(struct vfs_handle_struct *handle,
                                           const struct smb_filename *smb_fname,
                                           uint32_t dosmode)
{
	NTSTATUS ret;

	ret = set_dos_attributes_common(handle, smb_fname, dosmode);
                
        return ret;
}

static NTSTATUS ixnas_fset_dos_attributes(struct vfs_handle_struct *handle,
                                            struct files_struct *fsp,
                                            uint32_t dosmode)
{
	NTSTATUS ret;

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
uint32_t bsd2winperms(acl_perm_t bsd_perm)
{
	uint32_t winperms = 0;
	int l, m, h;
	l = m = h = 0;
	l = bsd_perm >> 3;
	m = bsd_perm >> 2;
	h = bsd_perm << 5;
	l &= (SMB_ACE4_READ_DATA|SMB_ACE4_WRITE_DATA|
	      SMB_ACE4_APPEND_DATA|SMB_ACE4_READ_NAMED_ATTRS|
	      SMB_ACE4_WRITE_NAMED_ATTRS);
	m &= (SMB_ACE4_WRITE_ATTRIBUTES|SMB_ACE4_READ_ATTRIBUTES|SMB_ACE4_DELETE_CHILD);
	h &= (SMB_ACE4_DELETE|SMB_ACE4_READ_ACL|
	      SMB_ACE4_WRITE_ACL|SMB_ACE4_WRITE_OWNER|
	      SMB_ACE4_SYNCHRONIZE); //remove bits lower than SMB_ACE4_DELETE
	winperms = (l|m|h);
	if (bsd_perm & ACL_EXECUTE) {
		//ACL_EXECUTE is 0x0001 and so it doesn't map cleanly. 
		winperms |= SEC_DIR_TRAVERSE;
	}

	return winperms;	
}

uint32_t win2bsdperms(uint32_t win_perm)
{
	uint32_t bsd_perm = 0;
	int l, m, h;
	l = m = h = 0;

	l =  win_perm << 3;
	m =  win_perm << 2;
	h =  win_perm >> 5;
	l &= (ACL_READ_DATA|ACL_WRITE_DATA|ACL_APPEND_DATA|
	      ACL_READ_NAMED_ATTRS|ACL_WRITE_NAMED_ATTRS);
	m &= (ACL_WRITE_ATTRIBUTES|ACL_READ_ATTRIBUTES|ACL_DELETE_CHILD); 
	h &= (ACL_READ_ACL|ACL_WRITE_ACL|ACL_WRITE_OWNER|ACL_DELETE); //Drop SYNCRHONIZE per#7909 
	bsd_perm = (l|m|h);
	if (win_perm & SEC_DIR_TRAVERSE) {
		bsd_perm |= ACL_EXECUTE; //0x0001 (doesn't map cleanly)
	}
	return bsd_perm;
}

uint16_t win2bsdflags(uint32_t win_flags, bool is_dir)
{
	uint16_t bsd_flags = 0;
	if (is_dir) {
		bsd_flags = win_flags & (ACL_ENTRY_FILE_INHERIT|
					 ACL_ENTRY_DIRECTORY_INHERIT|
					 ACL_ENTRY_NO_PROPAGATE_INHERIT|
					 ACL_ENTRY_INHERIT_ONLY);
	}
	if (win_flags & SEC_ACE_FLAG_INHERITED_ACE) {
		bsd_flags |= ACL_ENTRY_INHERITED;
	}
	return bsd_flags;
}

static bool bsdacl4_2win(TALLOC_CTX *mem_ctx,
	struct ixnas_config_data *config,
	const struct smb_filename *smb_fname,
	struct dom_sid *psid_owner,
	struct dom_sid *psid_group,
	struct security_ace **ppnt_ace_list,
	int *pgood_aces,
	uint16_t *acl_control_flags)
{
	int naces, i;
	bool is_dir, inherited_present;
	acl_t zacl;
	int good_aces = 0;
	is_dir = inherited_present = false;
	struct security_ace *nt_ace_list = NULL;

	zacl = acl_get_file(smb_fname->base_name, ACL_TYPE_NFS4);
	if ( zacl == NULL) {
		DBG_ERR("ixnas: acl_get_file() failed for %s: %s\n",
		smb_fname->base_name, strerror(errno));
		return false;
	}
	naces = zacl->ats_acl.acl_cnt;
	nt_ace_list = talloc_zero_array(mem_ctx, struct security_ace,
					2 * naces);
	if (nt_ace_list==NULL)
	{
		DBG_ERR("talloc error with %d aces", naces);
		errno = ENOMEM;
		acl_free(zacl);
		return false;
	}
	for(i=0; i<naces; i++) {
		uint32_t mask;
		uint32_t win_ace_flags;
		uint32_t win_ace_type;
		struct dom_sid sid;
		bool map_special_entry = false;
		DBG_DEBUG("ae_tag: %d, ae_id: %d, ae_perm: %x, "
			  "ae_flags: %x, ae_entry_type %x\n",
			  zacl->ats_acl.acl_entry[i].ae_tag,
			  zacl->ats_acl.acl_entry[i].ae_id,
			  zacl->ats_acl.acl_entry[i].ae_perm,
			  zacl->ats_acl.acl_entry[i].ae_flags,
			  zacl->ats_acl.acl_entry[i].ae_entry_type);

		if (!(zacl->ats_acl.acl_entry[i].ae_perm) &&
		    (zacl->ats_acl.acl_entry[i].ae_tag & ACL_EVERYONE)) {
			continue;
		}

		mask = bsd2winperms(zacl->ats_acl.acl_entry[i].ae_perm);

		win_ace_flags = zacl->ats_acl.acl_entry[i].ae_flags;

		/*
		 * NFSv4 flags map directly to NTFS flags with the exception
		 * of SEC_ACE_FLAG_INHERITED_ACE.
		 */
		if (zacl->ats_acl.acl_entry[i].ae_flags & ACL_ENTRY_INHERITED) {
			inherited_present = True;
			win_ace_flags |= SEC_ACE_FLAG_INHERITED_ACE;
		}

		win_ace_type = zacl->ats_acl.acl_entry[i].ae_entry_type >> 9; 

		/*
		 * Windows clients expect SEC_STD_SYNCHRONIZE to allow
		 * rename. See Samba bug #7909. This must not be added to
		 * DENY aces bug #8442.
		 */
		if (win_ace_type == SEC_ACE_TYPE_ACCESS_ALLOWED) {
			mask |= SEC_STD_SYNCHRONIZE;
		}

		switch (zacl->ats_acl.acl_entry[i].ae_tag) {
			case ACL_USER_OBJ:
				sid_copy(&sid, psid_owner);
				map_special_entry = True;
				break;
			case ACL_GROUP_OBJ:
				sid_copy(&sid, psid_group);
				map_special_entry = True;
				break;
			case ACL_EVERYONE:
				sid_copy(&sid, &global_sid_World);
				break;
			case ACL_GROUP:
				gid_to_sid(&sid, zacl->ats_acl.acl_entry[i].ae_id);
				break;
			default:
				uid_to_sid(&sid, zacl->ats_acl.acl_entry[i].ae_id);
				break;
		}
		if (map_special_entry) {
			/*
			 * Special handling for owner@, and group@ entries.
			 * These entries are split into two entries in the Windows SD.
			 * For the first entry owner@ and group@ are mapped to 
			 * S-1-3-0 and S-1-3-1 respectively. Their permset is not changed
			 * for these entries, but SEC_ACE_FLAG_INHERIT_ONLY is added 
			 * to the inheritance flags. The second entry is mapped to
			 * the SID associated with the UID or GID of the owner or group,
			 * and inheritance flags are stripped. This implements windows
			 * behavior for CREATOR-OWNER and CREATOR-GROUP.
			 */
			if ((zacl->ats_acl.acl_entry[i].ae_perm & ACL_WRITE_DATA) &&
			     config->zfs_acl_map_modify && !(zacl->ats_acl.acl_entry[i].ae_flags) &&
			     winac_ace_type == SEC_ACE_TYPE_ACCESS_ALLOWED) {
				/*
				 * Compatibilty logic for posix modes on
				 * special ids. for group, map "rw" to "modify". 
				 * for user, map "rw" to "full control".
				 */
				mask |= (SEC_STD_DELETE|
					 SEC_FILE_WRITE_EA|
					 SEC_FILE_WRITE_ATTRIBUTE);
			}

			if (!(win_ace_flags & SEC_ACE_FLAG_INHERIT_ONLY)) {
				uint32_t win_ace_flags_current;
				win_ace_flags_current = win_ace_flags &
					~(SEC_ACE_FLAG_OBJECT_INHERIT |
					  SEC_ACE_FLAG_CONTAINER_INHERIT);
				DBG_DEBUG("map current sid:: ace_type: %x, mask: %x, flags%x\n",
					  win_ace_type, mask, win_ace_flags_current);
				init_sec_ace(&nt_ace_list[good_aces++], &sid,
					win_ace_type, mask,
					win_ace_flags_current);
			}
			if ((zacl->ats_acl.acl_entry[i].ae_tag == ACL_USER_OBJ) &&
			     win_ace_flags & (SEC_ACE_FLAG_OBJECT_INHERIT |
					      SEC_ACE_FLAG_CONTAINER_INHERIT)) {
				uint32_t win_ace_flags_creator;
				win_ace_flags_creator = win_ace_flags |
					SEC_ACE_FLAG_INHERIT_ONLY;
				DBG_DEBUG("map creator owner:: ace_type: %x, mask: %x, flags%x\n",
					  win_ace_type, mask, win_ace_flags_creator);
				init_sec_ace(&nt_ace_list[good_aces++],
					&global_sid_Creator_Owner,
					win_ace_type, mask,
					win_ace_flags_creator);
			}
			if ((zacl->ats_acl.acl_entry[i].ae_tag == ACL_GROUP_OBJ) &&
			     win_ace_flags & (SEC_ACE_FLAG_OBJECT_INHERIT |
					      SEC_ACE_FLAG_CONTAINER_INHERIT)) {
				uint32_t win_ace_flags_creator;
				win_ace_flags_creator = win_ace_flags |
					SEC_ACE_FLAG_INHERIT_ONLY;
				DBG_DEBUG("map creator group:: ace_type: %x, mask: %x, flags%x\n",
					  win_ace_type, mask, win_ace_flags_creator);
				init_sec_ace(&nt_ace_list[good_aces++],
					&global_sid_Creator_Group,
					win_ace_type, mask,
					win_ace_flags_creator);
			}
		} else {
			DBG_DEBUG("map normal ace:: ace_type: %x, mask: %x, flags%x\n",
				  win_ace_type, mask, win_ace_flags);
			init_sec_ace(&nt_ace_list[good_aces++], &sid,
				     win_ace_type, mask, win_ace_flags);
		}
	}
	nt_ace_list = talloc_realloc(mem_ctx, nt_ace_list, struct security_ace,
				     good_aces);

	/* returns a NULL ace list when good_aces is zero. */
	if (good_aces && nt_ace_list == NULL) {
		DBG_DEBUG("realloc error with %d aces\n", good_aces);
		errno = ENOMEM;
		acl_free(zacl);
		return false;
	}
	*ppnt_ace_list = nt_ace_list;
	*pgood_aces = good_aces;
	if (inherited_present) {
		*acl_control_flags = (SEC_DESC_DACL_PROTECTED|
				     SEC_DESC_SELF_RELATIVE);
	}
	else {
		*acl_control_flags = (SEC_DESC_SELF_RELATIVE);
	}
	acl_free(zacl);
	return true;
}

static NTSTATUS ixnas_get_nt_acl_nfs4_common(struct connection_struct *conn,
					     TALLOC_CTX *mem_ctx,
					     const struct smb_filename *smb_fname,
					     struct security_descriptor **ppdesc,
					     uint32_t security_info,
					     struct ixnas_config_data *config)
{
	/*
	 * Converts native NFSv4 ACL into Windows Security Descriptor (SD)
	 * ACEs in the DACL in the SD map more or less directly to ZFS ACEs,
	 * SMB clients use SIDs and so all xIDs must be converted to SIDs.
	 * FreeBSD currently does not implement NFSv4.1 ACL control flags,
	 * and so special handling of the SEC_DESC_DACL_PROTECTED flag is
	 * required.
	 */
	int good_aces = 0;
	uint16_t acl_control_flags;
	struct dom_sid sid_owner, sid_group;
	size_t sd_size = 0;
	struct security_ace *nt_ace_list = NULL;
	struct security_acl *psa = NULL;
	struct security_descriptor *psd = NULL;
	TALLOC_CTX *frame = talloc_stackframe();
	SMB_STRUCT_STAT sbuf;
	int ret;
	bool ok;
        if (VALID_STAT(smb_fname->st)) {
                sbuf = smb_fname->st;
        }
	else {
		ret = vfs_stat_smb_basename(conn, smb_fname, &sbuf);
		if (ret != 0) {
			DBG_ERR("stat [%s]failed: %s\n",
				 smb_fname_str_dbg(smb_fname), strerror(errno));
			return map_nt_error_from_unix(errno);
		}
	}

	uid_to_sid(&sid_owner, sbuf.st_ex_uid);
	gid_to_sid(&sid_group, sbuf.st_ex_gid);

	ok = bsdacl4_2win(mem_ctx, config, smb_fname, &sid_owner, &sid_group,
                          &nt_ace_list, &good_aces, &acl_control_flags);

	if (!ok) {
		DBG_INFO("bsdacl4_2win failed\n");
		TALLOC_FREE(frame);
		return map_nt_error_from_unix(errno);
	}
	psa = make_sec_acl(frame, NT4_ACL_REVISION, good_aces, nt_ace_list);
	if (psa == NULL) {
		DBG_ERR("make_sec_acl failed\n");
		TALLOC_FREE(frame);
		return NT_STATUS_NO_MEMORY;
	}
	psd = make_sec_desc(
		mem_ctx, SD_REVISION, acl_control_flags,
		(security_info & SECINFO_OWNER) ? &sid_owner : NULL,
		(security_info & SECINFO_GROUP) ? &sid_group : NULL,
		NULL, psa, &sd_size);
	if (psd==NULL) {
		DBG_ERR("make_sec_desc failed\n");
		TALLOC_FREE(frame);
		return NT_STATUS_NO_MEMORY;
	}
	/*
	 * Optionally order the ACEs per guidelines here:
	 * https://docs.microsoft.com/en-us/windows/desktop/secauthz/order-of-aces-in-a-dacl
	 *
	 * The following steps describe the preferred order:
	 * 1. All explicit ACEs are placed in a group before any inherited ACEs.
	 * 2. Within the group of explicit ACEs, access-denied ACEs are placed before access-allowed ACEs.
	 * 3. Inherited ACEs are placed in the order in which they are inherited. ACEs inherited from
	 *    the child object's parent come first, then ACEs inherited from the grandparent, and so on
	 *    up the tree of objects.
	 * 4. For each level of inherited ACEs, access-denied ACEs are placed before access-allowed ACEs.
	 *
	 * This is potentially expensive and so is disabled by default, but may be required
	 * in environments where clients (perhaps using other filesharing protocols) may write
	 * ACLs with entries outside of the preferred order.
	 */
	if (psd->dacl && config->zfs_acl_sortaces) {
		dacl_sort_into_canonical_order(psd->dacl->aces, (unsigned int)psd->dacl->num_aces);
	}	
	*ppdesc = psd;
	DBG_DEBUG("sd size %d\n", (int)ndr_size_security_descriptor(*ppdesc, 0));
	TALLOC_FREE(frame);
	return NT_STATUS_OK;
}

/* zfs_set_nt_acl()
 * set the local file's acls obtaining it in NT form
 * using the NFSv4 format conversion
 */
static NTSTATUS ixnas_set_nfs4_acl(vfs_handle_struct *handle,
				   files_struct *fsp,
				   uint32_t security_info_sent,
				   const struct security_descriptor *psd,
				   struct ixnas_config_data *config)
{
	int ret, naces, i, saved_errno;
	naces = psd->dacl->num_aces;
	acl_t zacl;
	acl_entry_t hidden_entry;
	zacl = acl_init(ACL_MAX_ENTRIES);
	bool is_dir;
	uint32_t tmp_mask = 0;

	SMB_STRUCT_STAT sbuf;

	if (VALID_STAT(fsp->fsp_name->st)) {
		sbuf = fsp->fsp_name->st;
	}
	else {
		ret = vfs_stat_smb_basename(handle->conn, fsp->fsp_name, &sbuf);
		if (ret != 0) {
			DBG_DEBUG("stat [%s]failed: %s\n",
				fsp_str_dbg(fsp), strerror(errno));
			acl_free(zacl);
			return map_nt_error_from_unix(errno);
		}
	}
	is_dir = S_ISDIR(sbuf.st_ex_mode);
	for (i=0; i<psd->dacl->num_aces; i++) {
		acl_entry_t new_entry = NULL;
		acl_perm_t permset = 0;
		acl_entry_type_t type = 0;
		acl_flag_t flags = 0;
		uid_t id;
		acl_tag_t tag = 0;

		const struct security_ace *ace_nt = psd->dacl->aces +i; 
		DBG_DEBUG("[dacl entry] access_mask: 0x%x, flags: 0x%x, type: 0x%x\n",
			ace_nt->access_mask, ace_nt->flags, ace_nt->type); 
		tmp_mask = ace_nt->access_mask & (SEC_STD_ALL | SEC_FILE_ALL);
		se_map_generic(&tmp_mask, &file_generic_mapping);
		if (tmp_mask != ace_nt->access_mask)
			DBG_INFO("tmp_mask (0x%x) != access_mask(0x%x)\n",
				  tmp_mask, ace_nt->access_mask);
		permset = win2bsdperms(tmp_mask);
		flags = win2bsdflags(ace_nt->flags, is_dir);
		switch (ace_nt->type) {
			case SEC_ACE_TYPE_ACCESS_ALLOWED:
				type = ACL_ENTRY_TYPE_ALLOW;
				break;
			case SEC_ACE_TYPE_ACCESS_DENIED:
				type = ACL_ENTRY_TYPE_DENY;
				break;
			case SEC_ACE_TYPE_SYSTEM_AUDIT:
				type = ACL_ENTRY_TYPE_ALARM;
				break;
			case SEC_ACE_TYPE_SYSTEM_ALARM:
				type = ACL_ENTRY_TYPE_AUDIT;
				break;
			default:
				DBG_ERR("Unsupported aceType: %x\n", ace_nt->type);
				continue;
		}

		/*
		 * Convert SD trustee to ae_tag and ae_id. Implements nfs4:mode = simple 
		 *
		 * S-1-1-0 (World) is mapped to everyone@
		 * S-1-3-0 (Creator-Owner) and S-1-3-1 (Creator-Group) are mapped to .
		 * owner@ and group@ respectively, and set to "inherit only". If the entries
		 * do not have (CI|OI) then we don't add the entry to the ACL (INHERIT_ONLY
		 * without other inheritance flags is invalid). This is to implement Windows
		 * behavior for these SIDs.
		 *
		 * The SID is first attempted to map to a UID. This is because in ID_TYPE_BOTH
		 * SIDs will have a corresponding GID entry, but not a UID entry.
		 * If the mapped UID is identical to the owner of the file, and inheritance flags
		 * not set, then map the SID to owner@.
		 *
		 * Same logic applies to GID / group@.
		 *
		 * In all other cases, map the SID to the respective UID/GID and set appropriate
		 * ACL tag.
		 */
		if (dom_sid_equal(&ace_nt->trustee, &global_sid_World)) {
			tag  = ACL_EVERYONE;
			id   = ACL_UNDEFINED_ID;
		}
		else if (dom_sid_equal(&ace_nt->trustee, &global_sid_Creator_Owner)){
			tag  = ACL_USER_OBJ;
			id   = ACL_UNDEFINED_ID;
			flags |= ACL_ENTRY_INHERIT_ONLY;
			if (flags & !(ACL_ENTRY_FILE_INHERIT|ACL_ENTRY_DIRECTORY_INHERIT)) {
				continue;
			}
		}
		else if (dom_sid_equal(&ace_nt->trustee, &global_sid_Creator_Group)) {
			tag  = ACL_GROUP_OBJ;
			id   = ACL_UNDEFINED_ID;
			flags |= ACL_ENTRY_INHERIT_ONLY;
			if (flags & !(ACL_ENTRY_FILE_INHERIT|ACL_ENTRY_DIRECTORY_INHERIT)) {
				continue;
			}
		}	
		else {
			uid_t uid;
			gid_t gid;
			if (sid_to_uid(&ace_nt->trustee, &uid)) {
				if ((uid == sbuf.st_ex_uid) && 
				    (ace_nt->flags & !(SEC_ACE_FLAG_OBJECT_INHERIT|
						       SEC_ACE_FLAG_CONTAINER_INHERIT|
						       SEC_ACE_FLAG_INHERIT_ONLY))) {
					tag  = ACL_USER_OBJ;
					id   = ACL_UNDEFINED_ID;
				} 
				else {
					tag  = ACL_USER;
					id   = uid;
				}
			}
			else if (sid_to_gid(&ace_nt->trustee, &gid)) {
				if ((gid == sbuf.st_ex_gid) &&
				    (ace_nt->flags & !(SEC_ACE_FLAG_OBJECT_INHERIT|
						       SEC_ACE_FLAG_CONTAINER_INHERIT|
						       SEC_ACE_FLAG_INHERIT_ONLY))) {
					tag  = ACL_GROUP_OBJ;
					id   = ACL_UNDEFINED_ID;
					
				}
				else {
					tag  = ACL_GROUP;
					id   = gid;
				}
			}
			else if (dom_sid_compare_domain(&ace_nt->trustee, &global_sid_Unix_NFS) == 0) {
				continue;
			}
			else {
				DBG_ERR("ixnas: file [%s] could not convert to uid or gid\n",
					fsp->fsp_name->base_name);
				continue;
			}
		}
		DBG_DEBUG("tag: 0x%08x, id: %d, perm: 0x%08x, flags: 0x%04x, type: 0x%04x\n",
			tag, id, permset, flags, type); 
		
		if (acl_create_entry(&zacl, &new_entry) < 0) {
			DBG_ERR("Failed to create new ACL entry: %s\n", strerror(errno));
		}
		new_entry->ae_perm = permset;
		new_entry->ae_flags = flags;
		new_entry->ae_entry_type = type;
		new_entry->ae_tag = tag;
		new_entry->ae_id = id;
	}
	/*
	 * The 'hidden entry' is added to lock down ZFS behavior of appending
	 * special entries to ZFS ACL on file creation on absence of inheriting
	 * special entries in the parent directory.
	 */
	if (config->zfs_acl_ignore_empty_mode) {
		if (acl_create_entry(&zacl, &hidden_entry) < 0) {
			DBG_ERR("Failed to create new ACL entry: %s\n", strerror(errno));
		}
		if (is_dir) {
			hidden_entry->ae_flags = ACL_ENTRY_DIRECTORY_INHERIT|ACL_ENTRY_FILE_INHERIT;
		}
		else {
			hidden_entry->ae_flags = 0;
		}
		hidden_entry->ae_perm = 0;
		hidden_entry->ae_entry_type = ACL_ENTRY_TYPE_ALLOW;
		hidden_entry->ae_tag = ACL_EVERYONE;
		hidden_entry->ae_id = ACL_UNDEFINED_ID;
	}

	if(acl_set_file(fsp->fsp_name->base_name, ACL_TYPE_NFS4, zacl) < 0) {
		DBG_DEBUG("(acl_set_file(): %s): %s\n", fsp_str_dbg(fsp), strerror(errno));
		if ( pathconf(fsp->fsp_name->base_name, _PC_ACL_NFS4) < 0 ) {
			DBG_INFO("%s: pathconf(..., _PC_ACL_NFS4) failed. Path does not support NFS4 ACL.",
				fsp_str_dbg(fsp));
			errno = ENOSYS; //preserve behavior from libsunacl and zfsacl
		} 
		else {
			DBG_ERR("(acl_set_file(): %s): %s ", fsp_str_dbg(fsp),
				  strerror(errno));
		}
		saved_errno = errno;
		acl_free(zacl);
		errno = saved_errno;
		return map_nt_error_from_unix(errno);
	}
	acl_free(zacl);
	return NT_STATUS_OK;	
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

	status = ixnas_get_nt_acl_nfs4_common(handle->conn,
					      frame,
					      fsp->fsp_name,
					      ppdesc,
					      security_info,
					      config); 

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

	status = ixnas_get_nt_acl_nfs4_common(handle->conn,
					      mem_ctx,
					      smb_fname,
					      ppdesc,
					      security_info,
					      config); 

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

	TALLOC_FREE(frame);
	return status;
}

static int ixnas_get_file_owner(files_struct *fsp, SMB_STRUCT_STAT *psbuf)
{
	ZERO_STRUCTP(psbuf);

	if (fsp->fh->fd == -1) {
		if (vfs_stat_smb_basename(fsp->conn, fsp->fsp_name, psbuf) != 0) {
			DBG_ERR("vfs_stat_smb_basename failed with error %s\n",
				strerror(errno));
			return -1;
		}
		return 0;
	}
	if (SMB_VFS_FSTAT(fsp, psbuf) != 0)
	{
		DBG_ERR("SMB_VFS_FSTAT failed with error %s\n",
			strerror(errno));
		return -1;
	}

	return 0;
}

static NTSTATUS ixnas_fset_nt_acl(vfs_handle_struct *handle,
			 files_struct *fsp,
			 uint32_t security_info_sent,
			 const struct security_descriptor *psd)
{
	struct ixnas_config_data *config;
	NTSTATUS status;
	uid_t newUID = (uid_t)-1;
	gid_t newGID = (gid_t)-1;
	SMB_STRUCT_STAT sbuf;

	SMB_VFS_HANDLE_GET_DATA(handle, config,
				struct ixnas_config_data,
				return NT_STATUS_INTERNAL_ERROR);

	if (!config->zfs_acl_enabled) {
		return SMB_VFS_NEXT_FSET_NT_ACL(handle, fsp, security_info_sent, psd);
	}

	if (ixnas_get_file_owner(fsp, &sbuf)) {
		return map_nt_error_from_unix(errno);
	}

	if (config->nfs4_params.do_chown) {
		status = unpack_nt_owners(fsp->conn, &newUID, &newGID,
					  security_info_sent, psd);
		if (!NT_STATUS_IS_OK(status)) {
			DBG_INFO("unpack_nt_owners failed\n");
			return status;
		}
		if (((newUID != (uid_t)-1) && (sbuf.st_ex_uid != newUID)) ||
		    ((newGID != (gid_t)-1) && (sbuf.st_ex_gid != newGID))) {
			status = try_chown(fsp, newUID, newGID);
			if (!NT_STATUS_IS_OK(status)) {
				DBG_INFO("chown %s, %u, %u failed. Error = "
					 "%s.\n", fsp_str_dbg(fsp),
					 (unsigned int)newUID,
					 (unsigned int)newGID,
					 nt_errstr(status));
				return status;
			}
			DBG_DEBUG("chown %s, %u, %u succeeded.\n",
				  fsp_str_dbg(fsp), (unsigned int)newUID,
				  (unsigned int)newGID);
		}
	}

	if (!(security_info_sent & SECINFO_DACL) || psd->dacl ==NULL) {
		DBG_ERR("No dacl found: security_info_sent = 0x%x\n",
			security_info_sent);
		return NT_STATUS_OK;
 	}
	status = ixnas_set_nfs4_acl(handle, fsp, security_info_sent, psd, config);
	return status;
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

#if HAVE_LIBZFS
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
#endif

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

	/* 
	 * Ensure other alternate methods of mapping dosmodes are disabled.
	 */

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

	/* ZFS ACL PARAMETERS */
	config->zfs_acl_enabled = lp_parm_bool(SNUM(handle->conn),
			"ixnas", "zfs_acl_enabled", true);

	if (config->zfs_acl_enabled) {
		config->zfs_acl_map_modify = lp_parm_bool(SNUM(handle->conn),
			"ixnas", "zfsacl_map_modify", false);

		config->zfs_acl_map_modify = lp_parm_bool(SNUM(handle->conn),
			"ixnas", "zfsacl_ignore_empty_mode", false);
		
		config->zfs_acl_expose_snapdir = lp_parm_bool(SNUM(handle->conn),
			"ixnas", "zfsacl_expose_snapdir", true);	
		
		config->zfs_acl_sortaces = lp_parm_bool(SNUM(handle->conn),
			"ixnas", "zfsacl_sortaces", false);
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
		DBG_ERR("%s: Couldn't register custom debugging class!\n",
			"vfs_ixnas_init");
	} else {
		DBG_DEBUG("%s: Debug class number of '%s': %d\n",
		"vfs_ixnas_init","ixnas",vfs_ixnas_debug_level);
	}
}
