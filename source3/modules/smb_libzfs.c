/*-
 * Copyright 2018 iXsystems, Inc.
 * All rights reserved
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted providing that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 */

#define NEED_SOLARIS_BOOLEAN

#include <stdbool.h>
#include <talloc.h>
#include <sys/types.h>
#include <sys/time.h>
#include <libzfs.h>
#include "lib/util/debug.h"
#include "smb_macros.h"
#include "modules/smb_libzfs.h"

enum SMB_QUOTA_TYPE {
        SMB_INVALID_QUOTA_TYPE = -1,
        SMB_USER_FS_QUOTA_TYPE = 1,
        SMB_USER_QUOTA_TYPE = 2,
        SMB_GROUP_FS_QUOTA_TYPE = 3,/* not used yet */
        SMB_GROUP_QUOTA_TYPE = 4 /* used by disk_free queries */
};

int
smb_zfs_get_quota(char *path, int64_t xid, enum SMB_QUOTA_TYPE quota_type, uint64_t *hardlimit, uint64_t *usedspace)
{
	int ret;
	size_t blocksize = 1024;
	libzfs_handle_t *libzfsp;
	zfs_handle_t *zfsp;
	char u_req[256] = { 0 };
	char q_req[256] = { 0 };
	uint64_t quota, used; 
	quota = used = 0;

	DBG_DEBUG("Path: (%s), xid: %lu), qtype (%u)\n",
		path, xid, quota_type);

	switch (quota_type) {
	case SMB_USER_QUOTA_TYPE:
	case SMB_USER_FS_QUOTA_TYPE:
		snprintf(u_req, sizeof(u_req), "userused@%lu", xid);
		snprintf(q_req, sizeof(q_req), "userquota@%lu", xid);
		DBG_DEBUG("u_req: (%s), q_req (%s)\n", u_req, q_req);
		break;
	case SMB_GROUP_QUOTA_TYPE:
	case SMB_GROUP_FS_QUOTA_TYPE:
		snprintf(u_req, sizeof(u_req), "groupused@%lu", xid);
		snprintf(q_req, sizeof(q_req), "groupquota@%lu", xid);
		DBG_DEBUG("u_req: (%s), q_req (%s)\n", u_req, q_req);
		break;
	default:
		DBG_ERR("Received unknown quota type (%d)\n", quota_type);
		return (-1);
	}

	if (path == NULL) {
		DBG_ERR("Path does not exist\n");
		return (-1);
	}

	if ((libzfsp = libzfs_init()) == NULL) {
		DBG_ERR("Failed to init libzfs\n");
		return (-1);
	}

	libzfs_print_on_error(libzfsp, B_TRUE);

	zfsp = zfs_path_to_zhandle(libzfsp, path,
		ZFS_TYPE_VOLUME|ZFS_TYPE_DATASET|ZFS_TYPE_FILESYSTEM);

	if (zfsp == NULL) {
		DBG_ERR("Failed to convert path (%s) to zhandle\n", path);
		libzfs_fini(libzfsp);
		return (-1);
	}
	
	DBG_DEBUG("userused string: (%s), userquota string: (%s)\n", u_req, q_req);
	zfs_prop_get_userquota_int(zfsp, q_req, &quota);
	zfs_prop_get_userquota_int(zfsp, u_req, &used);

	zfs_close(zfsp);
	libzfs_fini(libzfsp);

	quota /= blocksize;
	used /= blocksize;

	*hardlimit = quota;
	*usedspace = used;

	return 0;
}

int
smb_zfs_set_quota(char *path, int64_t xid, enum SMB_QUOTA_TYPE quota_type, uint64_t hardlimit)
{
	size_t blocksize = 1024;
	libzfs_handle_t *libzfsp;
	zfs_handle_t *zfsp;
	char q_req[256] = { 0 };
	char quota[256] = { 0 };
	hardlimit *= blocksize;
	snprintf(quota, sizeof(quota), "%lu", hardlimit); 

	DBG_DEBUG("Path: (%s), xid: %lu), qtype (%u), limit (%lu)\n",
		path, xid, quota_type, hardlimit);
	switch (quota_type) {
	case SMB_USER_QUOTA_TYPE:
	case SMB_USER_FS_QUOTA_TYPE:
		snprintf(q_req, sizeof(q_req), "userquota@%lu", xid);
		DBG_DEBUG("userquota string is (%s)\n", q_req);
		break;
	case SMB_GROUP_QUOTA_TYPE:
	case SMB_GROUP_FS_QUOTA_TYPE:
		snprintf(q_req, sizeof(q_req), "groupquota@%lu", xid);
		DBG_DEBUG("groupquota string is (%s)\n", q_req);
		break;
	default:
		DBG_ERR("Received unknown quota type (%d)\n", quota_type);
		return (-1);
	}

	if (path == NULL) {
		DBG_ERR("smb_zfs_set_quota received NULL path\n");
		return (-1);
	}

	if ((libzfsp = libzfs_init()) == NULL) {
		DBG_ERR("libzfs_init failed\n");
		return (-1);
	}

	libzfs_print_on_error(libzfsp, B_TRUE);

	zfsp = zfs_path_to_zhandle(libzfsp, path,
		ZFS_TYPE_VOLUME|ZFS_TYPE_DATASET|ZFS_TYPE_FILESYSTEM);

	if (zfsp == NULL){
		DBG_ERR("Failed to convert path (%s) to zhandle\n", path);
		libzfs_fini(libzfsp);
		return (-1);
	}

	DBG_INFO("PREPARING: smb_zfs_set_quota: Set (%s = %s)\n", q_req, quota);
	if (zfs_prop_set(zfsp, q_req, quota) != 0) {
		DBG_ERR("Failed to set (%s = %s)\n", q_req, quota);
		zfs_close(zfsp);
		libzfs_fini(libzfsp);
		return (-1);
	}

	zfs_close(zfsp);
	libzfs_fini(libzfsp);

	DBG_ERR("smb_zfs_set_quota: Set (%s = %s)\n", q_req, quota);

	return 0;
}

uint64_t
smb_zfs_disk_free(char *path, uint64_t *bsize, uint64_t *dfree, uint64_t *dsize, uid_t euid)
{
	size_t blocksize = 1024;
	libzfs_handle_t *libzfsp;
	zfs_handle_t *zfsp;
	char uu_req[256];
	char uq_req[256];
	snprintf(uu_req, sizeof(uu_req), "userused@%u", euid);
	snprintf(uq_req, sizeof(uq_req), "userquota@%u", euid);
	
	uint64_t available, usedbysnapshots, usedbydataset,
		usedbychildren, usedbyrefreservation, real_used, total, 
		userquota, userused, userquotarem;

	if (path == NULL) {
		DBG_ERR("received NULL path\n");
		return (-1);
	}

	if ((libzfsp = libzfs_init()) == NULL) {
		DBG_ERR("libzfs_init failed\n");
		return (-1);
	}

	libzfs_print_on_error(libzfsp, B_TRUE);

	zfsp = zfs_path_to_zhandle(libzfsp, path,
		ZFS_TYPE_VOLUME|ZFS_TYPE_DATASET|ZFS_TYPE_FILESYSTEM);
	if (zfsp == NULL) {
		DBG_ERR("Failed to convert path (%s) to zhandle\n", path);
		libzfs_fini(libzfsp);
		return (-1);
	}

	available = zfs_prop_get_int(zfsp, ZFS_PROP_AVAILABLE);
	usedbysnapshots = zfs_prop_get_int(zfsp, ZFS_PROP_USEDSNAP);
	usedbydataset = zfs_prop_get_int(zfsp, ZFS_PROP_USEDDS);
	usedbychildren = zfs_prop_get_int(zfsp, ZFS_PROP_USEDCHILD);
	usedbyrefreservation = zfs_prop_get_int(zfsp, ZFS_PROP_USEDREFRESERV);
	zfs_prop_get_userquota_int(zfsp, uq_req, &userquota);
	zfs_prop_get_userquota_int(zfsp, uu_req, &userused);

	zfs_close(zfsp);
	libzfs_fini(libzfsp);

	real_used = usedbysnapshots + usedbydataset + usedbychildren;

	userquotarem = (userquota - userused) / blocksize;
	userquota /= blocksize;

	total = (real_used + available) / blocksize;
	available /= blocksize;

	*bsize = blocksize;
	if ( userquota && (available > userquotarem) ) {
		*dfree = userquotarem;
	}
	else {
		*dfree = available;
	}
	if ( userquota && (total > userquota) ) {
		*dsize = userquota;
	}
	else {
		*dsize = total;
	}

	return (*dfree);
}

int
smb_zfs_create_homedir(char *parent, const char *base, const char *quota)
{
	libzfs_handle_t *libzfsp;
	zfs_handle_t *zfsp;
	zfs_handle_t *new_zfsp;
	char *p = strdup(parent);
	const char *parent_dataset;
	char nd[PATH_MAX] = { 0 };
	if (parent == NULL) {
		return (-1);
	}

	if ((libzfsp = libzfs_init()) == NULL) {
		return (-1);
	}

	libzfs_print_on_error(libzfsp, B_TRUE);

	zfsp = zfs_path_to_zhandle(libzfsp, p,
		ZFS_TYPE_VOLUME|ZFS_TYPE_DATASET|ZFS_TYPE_FILESYSTEM);

	if (zfsp == NULL) {
		DBG_ERR("Failed to obtain zhandle on parent directory: (%s)\n", parent);
		libzfs_fini(libzfsp);
		return (-1);
	}
	parent_dataset = zfs_get_name(zfsp); 
	snprintf(nd, sizeof(nd), "%s/%s", parent_dataset, base);
  
	if (zfs_create(libzfsp, nd, ZFS_TYPE_DATASET, NULL) != 0){
		DBG_ERR("Failed to create dataset to path (%s)\n", nd);
		zfs_close(zfsp);
		libzfs_fini(libzfsp);
		return (-1);	
	} 
	zfs_close(zfsp);

	new_zfsp = zfs_open(libzfsp, nd, ZFS_TYPE_DATASET);

	if (new_zfsp == NULL) {
		DBG_ERR("Failed to obtain zhandle on new dataset: (%s)\n", nd);
		libzfs_fini(libzfsp);
		return (-1);
	}

	if (zfs_mount(new_zfsp, NULL, 0) != 0) {
		DBG_ERR("Failed to mount ZFS dataset (%s)\n", nd);
	}

	if (quota) {
		if (zfs_prop_set(new_zfsp, "quota", quota) != 0) {
			DBG_ERR("Failed to set quota to (%s)\n", quota);
		}
	}

	DBG_DEBUG("Created ZFS dataset (%s) with quota (%s)\n", nd, quota);

	zfs_close(new_zfsp);
	libzfs_fini(libzfsp);

	return 0;
}
