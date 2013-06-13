/* VFS-based union mounts for Linux
 *
 * Copyright (C) 2004-2007 IBM Corporation, IBM Deutschland Entwicklung GmbH.
 * Copyright (C) 2007-2009 Novell Inc.
 * Copyright (C) 2009-2012 Red Hat, Inc.
 *
 *   Author(s): Jan Blunck (j.blunck@tu-harburg.de)
 *              Valerie Aurora <vaurora@redhat.com>
 *              David Howells <dhowells@redhat.com>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; version 2
 * of the License.
 */

#include <linux/module.h>
#include <linux/fs.h>
#include <linux/mount.h>
#include <linux/fs_struct.h>
#include <linux/slab.h>
#include <linux/namei.h>
#include <linux/fsnotify.h>
#include <linux/xattr.h>

#include "union.h"

/**
 * union_alloc - allocate a union stack
 * @path: path of topmost directory
 *
 * Allocate a union_stack large enough to contain the maximum number
 * of layers in this union mount.
 */
static struct union_stack *union_alloc(struct path *topmost)
{
	unsigned int layers = topmost->dentry->d_sb->s_union_count;
	BUG_ON(!S_ISDIR(topmost->dentry->d_inode->i_mode));

	return kcalloc(sizeof(struct path), layers, GFP_KERNEL);
}

/**
 * d_free_unions - free all unions for this dentry
 * @dentry: topmost dentry in the union stack to remove
 *
 * This must be called when freeing a dentry.
 */
void d_free_unions(struct dentry *topmost)
{
	struct path *path;
	unsigned int i, layers = topmost->d_sb->s_union_count;

	if (!IS_DIR_UNIONED(topmost))
		return;

	for (i = 0; i < layers; i++) {
		path = union_find_dir(topmost, i);
		if (path->mnt)
			path_put(path);
	}
	kfree(topmost->d_union_stack);
	topmost->d_union_stack = NULL;
}

/**
 * union_add_dir - Add another layer to a unioned directory
 * @topmost: topmost directory
 * @lower: directory in the current layer
 * @layer: index of layer to add this at
 *
 * @layer counts starting at 0 for the dir below the topmost dir.
 *
 * This transfers the caller's references to the constituents of *lower to the
 * union stack.
 */
int union_add_dir(struct path *topmost, struct path *lower, unsigned layer)
{
	struct dentry *dentry = topmost->dentry;
	struct path *path;

	BUG_ON(layer >= dentry->d_sb->s_union_count);

	if (!dentry->d_union_stack)
		dentry->d_union_stack = union_alloc(topmost);
	if (!dentry->d_union_stack)
		return -ENOMEM;

	path = union_find_dir(dentry, layer);
	*path = *lower;
	return 0;
}

/**
 * union_copyup_xattr
 * @old: dentry of original file
 * @new: dentry of new copy
 *
 * Copy up extended attributes from the original file to the new one.
 *
 * XXX - Permissions?  For now, copying up every xattr.
 */
static int union_copyup_xattr(struct dentry *old, struct dentry *new)
{
	ssize_t list_size, size;
	char *buf, *name, *value;
	int error;

	/* Check for xattr support */
	if (!old->d_inode->i_op->getxattr ||
	    !new->d_inode->i_op->getxattr)
		return 0;

	/* Find out how big the list of xattrs is */
	list_size = vfs_listxattr(old, NULL, 0);
	if (list_size <= 0)
		return list_size;

	/* Allocate memory for the list */
	buf = kzalloc(list_size, GFP_KERNEL);
	if (!buf)
		return -ENOMEM;

	/* Allocate memory for the xattr's value */
	error = -ENOMEM;
	value = kmalloc(XATTR_SIZE_MAX, GFP_KERNEL);
	if (!value)
		goto out;

	/* Actually get the list of xattrs */
	list_size = vfs_listxattr(old, buf, list_size);
	if (list_size <= 0) {
		error = list_size;
		goto out_free_value;
	}

	for (name = buf; name < (buf + list_size); name += strlen(name) + 1) {
		/* XXX Locking? old is on read-only fs */
		size = vfs_getxattr(old, name, value, XATTR_SIZE_MAX);
		if (size <= 0) {
			error = size;
			goto out_free_value;
		}
		/* XXX do we really need to check for size overflow? */
		/* XXX locks new dentry, lock ordering problems? */
		error = vfs_setxattr(new, name, value, size, 0);
		if (error)
			goto out_free_value;
	}

out_free_value:
	kfree(value);
out:
	kfree(buf);
	return error;
}

/**
 * union_create_topmost_dir - Create a matching dir in the topmost file system
 * @parent - parent of target on topmost layer
 * @name - name of target
 * @topmost - path of target on topmost layer
 * @lower - path of source on lower layer
 *
 * As we lookup each directory on the lower layer of a union, we create a
 * matching directory on the topmost layer if it does not already exist.
 *
 * We don't use vfs_mkdir() for a few reasons: don't want to do the security
 * check, don't want to make the dir opaque, don't need to sanitize the mode.
 *
 * XXX - owner is wrong, set credentials properly
 * XXX - rmdir() directory on failure of xattr copyup
 * XXX - not atomic w/ respect to crash
 */
int union_create_topmost_dir(struct path *parent, struct qstr *name,
			     struct path *topmost, struct path *lower)
{
	struct inode *dir = parent->dentry->d_inode;
	int mode = lower->dentry->d_inode->i_mode;
	int error;

	BUG_ON(topmost->dentry->d_inode);

	/* XXX - Do we even need to check this? */
	if (!dir->i_op->mkdir)
		return -EPERM;

	error = mnt_want_write(parent->mnt);
	if (error)
		return error;

	error = dir->i_op->mkdir(dir, topmost->dentry, mode);
	if (error)
		goto out;

	error = union_copyup_xattr(lower->dentry, topmost->dentry);
	if (error)
		dput(topmost->dentry);

	fsnotify_mkdir(dir, topmost->dentry);
out:
	mnt_drop_write(parent->mnt);
	return error;
}
