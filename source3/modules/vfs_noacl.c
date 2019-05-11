/*
 *  Unix SMB/CIFS implementation.
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
#include "smbd/smbd.h"
#include "libcli/security/security.h"
#include "system/filesys.h"
#include <sys/acl.h>

static uint32_t noacl_fs_capabilities(struct vfs_handle_struct *handle,
			enum timestamp_set_resolution *p_ts_res)
{
	/*
	 * Remove flag for FILE_PERSISTENT_ACLS. MS-FSCC 2.5.1 defines as follows:
	 * "The file system preserves and enforces access control lists (ACLs)."
	 * Per MS-FSA Appendix A, this flag is set on ReFS and NTFS, but not
	 * FAT, EXFAT, UDFS, CDFS. 
	 */
	uint32_t fscaps = SMB_VFS_NEXT_FS_CAPABILITIES(handle, p_ts_res);
	fscaps &= ~FILE_PERSISTENT_ACLS;
	DBG_INFO("noacl: fscaps: %08x\n", fscaps);
	return fscaps;
}

static uint32_t fileflags_to_dosmode(uint32_t fileflags)
{
	uint32_t dosmode = 0;
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
	if (dosmode & FILE_ATTRIBUTE_SYSTEM) {
		fileflags |= UF_SYSTEM;
	}
	if (dosmode & FILE_ATTRIBUTE_SPARSE) {
		fileflags |= UF_SPARSE;
	}

	return fileflags;
}

static int write_dosmode_as_user(struct vfs_handle_struct *handle,
			 const struct smb_filename *smb_fname,
			 mode_t new_mode, uint32_t fileflags)
{
	int ret;
	ret = SMB_VFS_CHMOD(handle->conn, smb_fname, new_mode);
	if (ret != 0) {
		DBG_ERR("Setting dosmode readonly bit failed for %s: %s\n",
			smb_fname->base_name, strerror(errno));
		return ret;
	}
	ret = SMB_VFS_CHFLAGS(handle->conn, smb_fname, fileflags);
	if (ret != 0) {
		DBG_ERR("Setting dosmode failed for %s: %s\n",
			smb_fname->base_name, strerror(errno));
		return ret;
	}
	return ret;
}

static NTSTATUS set_dos_attributes_common(struct vfs_handle_struct *handle,
					 const struct smb_filename *smb_fname,
					 uint32_t dosmode)
{
	/*
	 * Use DOS READONLY to determine whether to add write bits to posix
	 * mode. Create mask parameter can be used to limit this to owner
	 * or group. Remaining DOS modes are mapped to file flags.
	 * Feature request specified that changes to DOS mode must be restricted
	 * to the file owner (not DOS semantics). This behavior will exist
	 * if the file has a trivial ACL because only the owner of the file will
	 * have FILE_WRITE_ATTRIBUTES.
	 */
	int ret;
	bool set_dosmode_ok = false;
	NTSTATUS status = NT_STATUS_OK;
	uint32_t fileflags = dosmode_to_fileflags(dosmode);
	mode_t new_mode = smb_fname->st.st_ex_mode;

	DBG_INFO("noacl:set_dos_attributes: set attribute 0x%x, on file %s\n",
		dosmode, smb_fname->base_name);


	if (IS_DOS_READONLY(dosmode)) {
		new_mode &= ~(S_IWUSR | S_IWGRP | S_IWOTH);
		}
	else {
		new_mode |= (S_IWUSR | S_IWGRP | S_IWOTH);
	}

	if (IS_DOS_DIR(dosmode)) {
		new_mode |= (S_IXUSR | S_IXGRP | S_IXOTH);
		new_mode &= lp_directory_mask(SNUM(handle->conn));
		new_mode |= lp_force_directory_mode(SNUM(handle->conn));
	}
	else {
		new_mode &= lp_create_mask(SNUM(handle->conn));
		new_mode |= lp_force_create_mode(SNUM(handle->conn));
	}
	
	if (!CAN_WRITE(handle->conn)) {
		return NT_STATUS_ACCESS_DENIED;
	}

 	status = smbd_check_access_rights(handle->conn, smb_fname, false,
					  FILE_WRITE_ATTRIBUTES);
	if (!NT_STATUS_IS_OK(status)) {
		DBG_WARNING("User %d lacks permissions to write new dosmode\n", geteuid());
		return status;
	}

	become_root();
	ret = write_dosmode_as_user(handle, smb_fname, new_mode, fileflags);
	unbecome_root();
	if (ret == -1) {
		DBG_WARNING("Setting dosmode failed for %s: %s\n",
			smb_fname->base_name, strerror(errno));
		return map_nt_error_from_unix(errno);
	}

	return NT_STATUS_OK;
}

static NTSTATUS noacl_get_dos_attributes(struct vfs_handle_struct *handle,
					 struct smb_filename *smb_fname,
					 uint32_t *dosmode)
{
	if ((smb_fname->st.st_ex_mode & (S_IWUSR | S_IWGRP | S_IWOTH)) == 0) {
		*dosmode |= FILE_ATTRIBUTE_READONLY;
	}
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

static NTSTATUS noacl_fget_dos_attributes(struct vfs_handle_struct *handle,
                                            struct files_struct *fsp,
                                            uint32_t *dosmode)
{
	if ((fsp->fsp_name->st.st_ex_mode & (S_IWUSR | S_IWGRP | S_IWOTH)) == 0) {
		*dosmode |= FILE_ATTRIBUTE_READONLY;
	}
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

static NTSTATUS noacl_set_dos_attributes(struct vfs_handle_struct *handle,
                                           const struct smb_filename *smb_fname,
                                           uint32_t dosmode)
{
	NTSTATUS ret;

	ret = set_dos_attributes_common(handle, smb_fname, dosmode);

	return ret;
}

static NTSTATUS noacl_fset_dos_attributes(struct vfs_handle_struct *handle,
                                            struct files_struct *fsp,
                                            uint32_t dosmode)
{
	NTSTATUS ret;

	ret = set_dos_attributes_common(handle, fsp->fsp_name, dosmode);

	return ret;
}

static NTSTATUS noacl_fset_nt_acl(vfs_handle_struct *handle,
			 files_struct *fsp,
			 uint32_t security_info_sent,
			 const struct security_descriptor *psd)
{
	return NT_STATUS_ACCESS_DENIED;
}

static SMB_ACL_T noacl_fail__sys_acl_get_file(vfs_handle_struct *handle,
					const struct smb_filename *smb_fname,
					SMB_ACL_TYPE_T type,
					TALLOC_CTX *mem_ctx)
{
	return (SMB_ACL_T)NULL;
}

static SMB_ACL_T noacl_fail__sys_acl_get_fd(vfs_handle_struct *handle,
					     files_struct *fsp,
					     TALLOC_CTX *mem_ctx)
{
	return (SMB_ACL_T)NULL;
}

static int noacl_fail__sys_acl_set_file(vfs_handle_struct *handle,
					 const struct smb_filename *smb_fname,
					 SMB_ACL_TYPE_T type,
					 SMB_ACL_T theacl)
{
	return -1;
}

static int noacl_fail__sys_acl_set_fd(vfs_handle_struct *handle,
				       files_struct *fsp,
				       SMB_ACL_T theacl)
{
	return -1;
}

static int noacl_fail__sys_acl_delete_def_file(vfs_handle_struct *handle,
			const struct smb_filename *smb_fname)
{
	return -1;
}

static int noacl_fail__sys_acl_blob_get_file(vfs_handle_struct *handle,
			const struct smb_filename *smb_fname,
			TALLOC_CTX *mem_ctx,
			char **blob_description,
			DATA_BLOB *blob)
{
	return -1;
}

static int noacl_fail__sys_acl_blob_get_fd(vfs_handle_struct *handle, files_struct *fsp, TALLOC_CTX *mem_ctx, char **blob_description, DATA_BLOB *blob)
{
	return -1;
}


static int noacl_connect(struct vfs_handle_struct *handle,
			    const char *service, const char *user)
{
	
	acl_t connectpath_acl;
	int trivial, ret;
	connectpath_acl = acl_get_file(handle->conn->connectpath, ACL_TYPE_NFS4);
	if (connectpath_acl == NULL) {
		DBG_ERR("noacl: acl_get_file() failed for %s: %s\n",
			handle->conn->connectpath, strerror(errno));
		return -1;
	}
	if (acl_is_trivial_np(connectpath_acl, &trivial) != 0) {
		DBG_ERR("noacl: acl_is_trivial() failed for %s: %s\n",
			handle->conn->connectpath, strerror(errno));
		acl_free(connectpath_acl);
		return -1;
	} 
	acl_free(connectpath_acl);
	if (trivial == 0) {
		DBG_ERR("noacl: non-trivial ACL detected on conncectpath %s. Denying access to share\n",
			handle->conn->connectpath, strerror(errno));
		return -1;
	}

	if ((lp_map_readonly(SNUM(handle->conn))) == MAP_READONLY_YES) {
		DBG_INFO("noacl:dosmode to file flag mapping enabled,"
			  "disabling 'map readonly'\n");
		lp_do_parameter(SNUM(handle->conn), "map readonly",
				"no");
	}

	if (lp_map_archive(SNUM(handle->conn))) {
		DBG_INFO("noacl:dosmode to file flag mapping enabled,"
			  "disabling 'map archive'\n");
		lp_do_parameter(SNUM(handle->conn), "map archive",
				"no");
	}
	return SMB_VFS_NEXT_CONNECT(handle, service, user);
}

static struct vfs_fn_pointers noacl_fns = {
	.fs_capabilities_fn = noacl_fs_capabilities,
	.connect_fn = noacl_connect,
	.get_dos_attributes_fn = noacl_get_dos_attributes,
	.fget_dos_attributes_fn = noacl_fget_dos_attributes,
	.set_dos_attributes_fn = noacl_set_dos_attributes,
	.fset_dos_attributes_fn = noacl_fset_dos_attributes,
	.fset_nt_acl_fn = noacl_fset_nt_acl,
	.sys_acl_get_file_fn = noacl_fail__sys_acl_get_file,
	.sys_acl_get_fd_fn = noacl_fail__sys_acl_get_fd,
	.sys_acl_blob_get_file_fn = noacl_fail__sys_acl_blob_get_file,
	.sys_acl_blob_get_fd_fn = noacl_fail__sys_acl_blob_get_fd,
	.sys_acl_set_file_fn = noacl_fail__sys_acl_set_file,
	.sys_acl_set_fd_fn = noacl_fail__sys_acl_set_fd,
	.sys_acl_delete_def_file_fn = noacl_fail__sys_acl_delete_def_file,
};

NTSTATUS vfs_noacl_init(TALLOC_CTX *);
NTSTATUS vfs_noacl_init(TALLOC_CTX *ctx)
{
	return smb_register_vfs(SMB_VFS_INTERFACE_VERSION, "noacl",
				&noacl_fns);
}
