// SPDX-License-Identifier: GPL-2.0-or-later
/* FS-Cache interface to CacheFiles
 *
 * Copyright (C) 2007 Red Hat, Inc. All Rights Reserved.
 * Written by David Howells (dhowells@redhat.com)
 */

#include <linux/slab.h>
#include <linux/mount.h>
#include <linux/xattr.h>
#include <linux/file.h>
#include <linux/falloc.h>
#include <trace/events/fscache.h>
#include "internal.h"

static atomic_t cachefiles_object_debug_id;

static int cachefiles_attr_changed(struct cachefiles_object *object);

/*
 * Allocate a cache object record.
 */
static
struct cachefiles_object *cachefiles_alloc_object(struct fscache_cookie *cookie)
{
	struct fscache_volume *vcookie = cookie->volume;
	struct cachefiles_object *object;
	struct cachefiles_volume *volume = vcookie->cache_priv;
	int n_accesses;

	_enter("{%s},%x,", vcookie->key, cookie->debug_id);

	object = kmem_cache_zalloc(cachefiles_object_jar, cachefiles_gfp);
	if (!object)
		return NULL;

	atomic_set(&object->usage, 1);

	spin_lock_init(&object->lock);
	INIT_LIST_HEAD(&object->cache_link);
	object->volume = volume;
	object->debug_id = atomic_inc_return(&cachefiles_object_debug_id);
	object->cookie = fscache_get_cookie(cookie, fscache_cookie_get_attach_object);
	rwlock_init(&object->content_map_lock);

	atomic_inc(&vcookie->cache->object_count);
	trace_cachefiles_ref(object->debug_id, cookie->debug_id, 1,
			     cachefiles_obj_new);

	/* Get a ref on the cookie and keep its n_accesses counter raised by 1
	 * to prevent wakeups from transitioning it to 0 until we're
	 * withdrawing caching services from it.
	 */
	n_accesses = atomic_inc_return(&cookie->n_accesses);
	trace_fscache_access(cookie->debug_id, refcount_read(&cookie->ref),
			     n_accesses, fscache_access_cache_pin);
	set_bit(FSCACHE_COOKIE_NACC_ELEVATED, &cookie->flags);
	return object;
}

/*
 * Attempt to look up the nominated node in this cache
 */
static bool cachefiles_lookup_cookie(struct fscache_cookie *cookie)
{
	struct cachefiles_object *object;
	struct cachefiles_cache *cache = cookie->volume->cache->cache_priv;
	const struct cred *saved_cred;
	bool success;

	object = cachefiles_alloc_object(cookie);
	if (!object)
		goto fail;

	_enter("{OBJ%x}", object->debug_id);

	if (!cachefiles_cook_key(object))
		goto fail_put;

	cookie->cache_priv = object;

	/* look up the key, creating any missing bits */
	cachefiles_begin_secure(cache, &saved_cred);
	success = cachefiles_look_up_object(object);
	cachefiles_end_secure(cache, saved_cred);

	if (!success)
		goto fail_withdraw;

	cachefiles_see_object(object, cachefiles_obj_see_lookup_cookie);

	spin_lock(&cache->object_list_lock);
	list_add(&object->cache_link, &cache->object_list);
	spin_unlock(&cache->object_list_lock);
	cachefiles_attr_changed(object);
	_leave(" = t");
	return true;

fail_withdraw:
	cachefiles_see_object(object, cachefiles_obj_see_lookup_failed);
	clear_bit(FSCACHE_COOKIE_IS_CACHING, &object->flags);
	fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_FAILED);
	kdebug("failed c=%08x o=%08x", cookie->debug_id, object->debug_id);
	/* The caller holds an access count on the cookie, so we need them to
	 * drop it before we can withdraw the object.
	 */
	return false;

fail_put:
	cachefiles_put_object(object, cachefiles_obj_put_alloc_fail);
fail:
	return false;
}

/*
 * Note that an object has been seen.
 */
void cachefiles_see_object(struct cachefiles_object *object,
			   enum cachefiles_obj_ref_trace why)
{
	trace_cachefiles_ref(object->debug_id, object->cookie->debug_id,
			     atomic_read(&object->usage), why);
}

/*
 * increment the usage count on an inode object (may fail if unmounting)
 */
struct cachefiles_object *cachefiles_grab_object(struct cachefiles_object *object,
						 enum cachefiles_obj_ref_trace why)
{
	int u;

	u = atomic_inc_return(&object->usage);
	trace_cachefiles_ref(object->debug_id, object->cookie->debug_id, u, why);
	return object;
}

/*
 * Shorten the backing object to discard any dirty data and free up
 * any unused granules.
 */
static bool cachefiles_shorten_object(struct cachefiles_object *object,
				      struct file *file, loff_t new_size)
{
	struct cachefiles_cache *cache = object->volume->cache;
	struct inode *inode = file_inode(file);
	loff_t i_size, dio_size;
	int ret;

	dio_size = round_up(new_size, CACHEFILES_DIO_BLOCK_SIZE);
	i_size = i_size_read(inode);

	trace_cachefiles_trunc(object, inode, i_size, dio_size,
			       cachefiles_trunc_shrink);
	ret = vfs_truncate(&file->f_path, dio_size);
	if (ret < 0) {
		cachefiles_io_error_obj(object, "Trunc-to-size failed %d", ret);
		cachefiles_remove_object_xattr(cache, file->f_path.dentry);
		return false;
	}

	if (new_size < dio_size) {
		trace_cachefiles_trunc(object, inode, dio_size, new_size,
				       cachefiles_trunc_dio_adjust);
		ret = vfs_fallocate(file, FALLOC_FL_ZERO_RANGE,
				    new_size, dio_size);
		if (ret < 0) {
			cachefiles_io_error_obj(object, "Trunc-to-dio-size failed %d", ret);
			cachefiles_remove_object_xattr(cache, file->f_path.dentry);
			return false;
		}
	}

	return true;
}

/*
 * Resize the backing object.
 */
static void cachefiles_resize_cookie(struct netfs_cache_resources *cres,
				     loff_t new_size)
{
	struct cachefiles_object *object = cachefiles_cres_object(cres);
	struct cachefiles_cache *cache = object->volume->cache;
	struct fscache_cookie *cookie = object->cookie;
	const struct cred *saved_cred;
	struct file *file = cachefiles_cres_file(cres);
	loff_t old_size = cookie->object_size;

	_enter("%llu->%llu", old_size, new_size);

	if (new_size < old_size) {
		cachefiles_begin_secure(cache, &saved_cred);
		cachefiles_shorten_content_map(object, new_size);
		cachefiles_shorten_object(object, file, new_size);
		cachefiles_end_secure(cache, saved_cred);
		object->cookie->object_size = new_size;
		return;
	}

	/* The file is being expanded.  We don't need to do anything
	 * particularly.  cookie->initial_size doesn't change and so the point
	 * at which we have to download before doesn't change.
	 */
	cookie->object_size = new_size;
}

/*
 * Commit changes to the object as we drop it.
 */
static void cachefiles_commit_object(struct cachefiles_object *object,
				     struct cachefiles_cache *cache)
{
	bool update = false;

	if (object->content_map_changed)
		cachefiles_save_content_map(object);
	if (test_and_clear_bit(FSCACHE_COOKIE_NEEDS_UPDATE, &object->cookie->flags))
		update = true;
	if (update)
		cachefiles_set_object_xattr(object);

	if (test_bit(CACHEFILES_OBJECT_USING_TMPFILE, &object->flags))
		cachefiles_commit_tmpfile(cache, object);
}

/*
 * Finalise and object and close the VFS structs that we have.
 */
static void cachefiles_clean_up_object(struct cachefiles_object *object,
				       struct cachefiles_cache *cache)
{
	if (test_bit(FSCACHE_COOKIE_RETIRED, &object->cookie->flags)) {
		if (!test_bit(CACHEFILES_OBJECT_USING_TMPFILE, &object->flags)) {
			cachefiles_see_object(object, cachefiles_obj_see_clean_delete);
			_debug("- inval object OBJ%x", object->debug_id);
			cachefiles_delete_object(object, FSCACHE_OBJECT_WAS_RETIRED);
		} else {
			cachefiles_see_object(object, cachefiles_obj_see_clean_drop_tmp);
			_debug("- inval object OBJ%x tmpfile", object->debug_id);
		}
	} else {
		cachefiles_see_object(object, cachefiles_obj_see_clean_commit);
		cachefiles_commit_object(object, cache);
	}

	cachefiles_unmark_inode_in_use(object);
	if (object->file) {
		fput(object->file);
		object->file = NULL;
	}
}

/*
 * Withdraw caching for a cookie.
 */
static void cachefiles_withdraw_cookie(struct fscache_cookie *cookie)
{
	struct cachefiles_object *object = cookie->cache_priv;
	struct cachefiles_cache *cache = object->volume->cache;
	const struct cred *saved_cred;

	_enter("o=%x", object->debug_id);
	cachefiles_see_object(object, cachefiles_obj_see_withdraw_cookie);

	if (!list_empty(&object->cache_link)) {
		spin_lock(&cache->object_list_lock);
		cachefiles_see_object(object, cachefiles_obj_see_withdrawal);
		clear_bit(FSCACHE_COOKIE_IS_CACHING, &object->flags);
		list_del_init(&object->cache_link);
		spin_unlock(&cache->object_list_lock);
	}

	if (object->file) {
		cachefiles_begin_secure(cache, &saved_cred);
		cachefiles_clean_up_object(object, cache);
		cachefiles_end_secure(cache, saved_cred);
	}

	cookie->cache_priv = NULL;
	cachefiles_put_object(object, cachefiles_obj_put_detach);
}

/*
 * dispose of a reference to an object
 */
void cachefiles_put_object(struct cachefiles_object *object,
			   enum cachefiles_obj_ref_trace why)
{
	unsigned int object_debug_id = object->debug_id;
	unsigned int cookie_debug_id = object->cookie->debug_id;
	struct fscache_cache *cache;
	int u;

	u = atomic_dec_return(&object->usage);
	trace_cachefiles_ref(object_debug_id, cookie_debug_id, u, why);
	if (u == 0) {
		_debug("- kill object OBJ%x", object_debug_id);

		ASSERTCMP(object->file, ==, NULL);

		kfree(object->d_name);

		cache = object->volume->cache->cache;
		fscache_put_cookie(object->cookie, fscache_cookie_put_object);
		object->cookie = NULL;

		kfree(object->content_map);
		kmem_cache_free(cachefiles_object_jar, object);
		if (atomic_dec_and_test(&cache->object_count))
			wake_up_all(&cachefiles_clearance_wq);
	}

	_leave("");
}

/*
 * sync a cache
 */
void cachefiles_sync_cache(struct cachefiles_cache *cache)
{
	const struct cred *saved_cred;
	int ret;

	_enter("%s", cache->cache->name);

	/* make sure all pages pinned by operations on behalf of the netfs are
	 * written to disc */
	cachefiles_begin_secure(cache, &saved_cred);
	down_read(&cache->mnt->mnt_sb->s_umount);
	ret = sync_filesystem(cache->mnt->mnt_sb);
	up_read(&cache->mnt->mnt_sb->s_umount);
	cachefiles_end_secure(cache, saved_cred);

	if (ret == -EIO)
		cachefiles_io_error(cache,
				    "Attempt to sync backing fs superblock returned error %d",
				    ret);
}

/*
 * notification the attributes on an object have changed
 * - called with reads/writes excluded by FS-Cache
 */
static int cachefiles_attr_changed(struct cachefiles_object *object)
{
	struct cachefiles_cache *cache = object->volume->cache;
	const struct cred *saved_cred;
	struct iattr newattrs;
	struct file *file = object->file;
	uint64_t ni_size;
	loff_t oi_size;
	int ret;

	ni_size = object->cookie->object_size;
	ni_size = round_up(ni_size, CACHEFILES_DIO_BLOCK_SIZE);

	_enter("{OBJ%x},[%llu]",
	       object->debug_id, (unsigned long long) ni_size);

	if (!file)
		return -ENOBUFS;

	oi_size = i_size_read(file_inode(file));
	if (oi_size == ni_size)
		return 0;

	cachefiles_begin_secure(cache, &saved_cred);
	inode_lock(file_inode(file));

	/* if there's an extension to a partial page at the end of the backing
	 * file, we need to discard the partial page so that we pick up new
	 * data after it */
	if (oi_size & ~PAGE_MASK && ni_size > oi_size) {
		_debug("discard tail %llx", oi_size);
		newattrs.ia_valid = ATTR_SIZE;
		newattrs.ia_size = oi_size & PAGE_MASK;
		ret = notify_change(&init_user_ns, file->f_path.dentry,
				    &newattrs, NULL);
		if (ret < 0)
			goto truncate_failed;
	}

	newattrs.ia_valid = ATTR_SIZE;
	newattrs.ia_size = ni_size;
	ret = notify_change(&init_user_ns, file->f_path.dentry, &newattrs, NULL);

truncate_failed:
	inode_unlock(file_inode(file));
	cachefiles_end_secure(cache, saved_cred);

	if (ret == -EIO) {
		cachefiles_io_error_obj(object, "Size set failed");
		ret = -ENOBUFS;
	}

	_leave(" = %d", ret);
	return ret;
}

/*
 * Invalidate the storage associated with a cookie.
 */
static bool cachefiles_invalidate_cookie(struct fscache_cookie *cookie)
{
	struct cachefiles_object *object = cookie->cache_priv;
	struct file *new_file, *old_file;
	u8 *map, *old_map;
	size_t map_size;
	bool old_tmpfile;

	_enter("o=%x,[%llu]", object->debug_id, object->cookie->object_size);

	old_tmpfile = test_bit(CACHEFILES_OBJECT_USING_TMPFILE, &object->flags);

	if (!object->file) {
		fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_ACTIVE);
		_leave(" = t [light]");
		return true;
	}

	new_file = cachefiles_create_tmpfile(object);
	if (IS_ERR(new_file))
		goto failed;

	map = cachefiles_new_content_map(object, &map_size);
	if (IS_ERR(map))
		goto failed_fput;

	/* Substitute the VFS target */
	_debug("sub");
	spin_lock(&object->lock);
	write_lock_bh(&object->content_map_lock);

	old_file = object->file;
	old_map = object->content_map;
	object->file			= new_file;
	object->content_map		= map;
	object->content_map_size	= map_size;
	object->content_map_changed	= true;
	object->content_info		= CACHEFILES_CONTENT_NO_DATA;
	set_bit(CACHEFILES_OBJECT_USING_TMPFILE, &object->flags);
	set_bit(FSCACHE_COOKIE_NEEDS_UPDATE, &object->cookie->flags);

	write_unlock_bh(&object->content_map_lock);
	spin_unlock(&object->lock);
	_debug("subbed");

	/* Allow I/O to take place again */
	fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_ACTIVE);
	kfree(old_map);

	if (old_file) {
		if (!old_tmpfile) {
			struct cachefiles_volume *volume = object->volume;
			struct dentry *fan = volume->fanout[(u8)object->key_hash];

			inode_lock_nested(d_inode(fan), I_MUTEX_PARENT);
			cachefiles_bury_object(volume->cache, object, fan,
					       old_file->f_path.dentry,
					       FSCACHE_OBJECT_INVALIDATED);
		}
		fput(old_file);
	}

	_leave(" = t");
	return true;

failed_fput:
	fput(new_file);
failed:
	fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_FAILED);
	_leave(" = f");
	return false;
}

const struct fscache_cache_ops cachefiles_cache_ops = {
	.name			= "cachefiles",
	.acquire_volume		= cachefiles_acquire_volume,
	.free_volume		= cachefiles_free_volume,
	.lookup_cookie		= cachefiles_lookup_cookie,
	.withdraw_cookie	= cachefiles_withdraw_cookie,
	.invalidate_cookie	= cachefiles_invalidate_cookie,
	.resize_cookie		= cachefiles_resize_cookie,
	.begin_operation	= cachefiles_begin_operation,
};
