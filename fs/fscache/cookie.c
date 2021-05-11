// SPDX-License-Identifier: GPL-2.0-or-later
/* netfs cookie management
 *
 * Copyright (C) 2004-2007, 2020 Red Hat, Inc. All Rights Reserved.
 * Written by David Howells (dhowells@redhat.com)
 *
 * See Documentation/filesystems/caching/netfs-api.rst for more information on
 * the netfs API.
 */

#define FSCACHE_DEBUG_LEVEL COOKIE
#include <linux/module.h>
#include <linux/slab.h>
#include "internal.h"

struct kmem_cache *fscache_cookie_jar;

#define fscache_cookie_hash_shift 15
static struct hlist_bl_head fscache_cookie_hash[1 << fscache_cookie_hash_shift];
static LIST_HEAD(fscache_cookies);
static DEFINE_RWLOCK(fscache_cookies_lock);
static const char fscache_cookie_stages[FSCACHE_COOKIE_STAGE__NR] = "-LAIFRD";

void fscache_print_cookie(struct fscache_cookie *cookie, char prefix)
{
	const u8 *k;

	pr_err("%c-cookie c=%08x [fl=%lx na=%u nA=%u]\n",
	       prefix,
	       cookie->debug_id,
	       cookie->flags,
	       atomic_read(&cookie->n_active),
	       atomic_read(&cookie->n_accesses));
	pr_err("%c-cookie V=%08x [%s]\n",
	       prefix,
	       cookie->volume->debug_id,
	       cookie->volume->key);

	k = (cookie->key_len <= sizeof(cookie->inline_key)) ?
		cookie->inline_key : cookie->key;
	pr_err("%c-key=[%u] '%*phN'\n", prefix, cookie->key_len, cookie->key_len, k);
}

static void fscache_free_cookie(struct fscache_cookie *cookie)
{
	write_lock(&fscache_cookies_lock);
	list_del(&cookie->proc_link);
	write_unlock(&fscache_cookies_lock);
	if (cookie->aux_len > sizeof(cookie->inline_aux))
		kfree(cookie->aux);
	if (cookie->key_len > sizeof(cookie->inline_key))
		kfree(cookie->key);
	fscache_stat_d(&fscache_n_cookies);
	kmem_cache_free(fscache_cookie_jar, cookie);
}

/*
 * Mark the end of an access on a cookie.
 */
void fscache_end_cookie_access(struct fscache_cookie *cookie,
			       enum fscache_access_trace why)
{
	int n_accesses;

	smp_mb__before_atomic();
	n_accesses = atomic_dec_return(&cookie->n_accesses);
	trace_fscache_access(cookie->debug_id, refcount_read(&cookie->ref),
			     n_accesses, why);
	if (n_accesses == 0)
		wake_up_var(&cookie->n_accesses);
}
EXPORT_SYMBOL(fscache_end_cookie_access);

/*
 * Pin the cache behind a cookie so that we can access it.
 */
static void __fscache_begin_cookie_access(struct fscache_cookie *cookie,
					  enum fscache_access_trace why)
{
	int n_accesses;

	n_accesses = atomic_inc_return(&cookie->n_accesses);
	smp_mb__after_atomic(); /* (Future) read stage after is-caching.
				 * Reread n_accesses after is-caching
				 */
	trace_fscache_access(cookie->debug_id, refcount_read(&cookie->ref),
			     n_accesses, why);
}

/*
 * Pin the cache behind a cookie so that we can access it.
 */
bool fscache_begin_cookie_access(struct fscache_cookie *cookie,
				 enum fscache_access_trace why)
{
	if (!test_bit(FSCACHE_COOKIE_IS_CACHING, &cookie->flags))
		return false;
	__fscache_begin_cookie_access(cookie, why);
	if (!test_bit(FSCACHE_COOKIE_IS_CACHING, &cookie->flags) ||
	    !fscache_cache_is_live(cookie->volume->cache)) {
		fscache_end_cookie_access(cookie, fscache_access_unlive);
		return false;
	}
	return true;
}

static inline void wake_up_cookie_stage(struct fscache_cookie *cookie)
{
	/* Use a barrier to ensure that waiters see the stage variable
	 * change, as spin_unlock doesn't guarantee a barrier.
	 *
	 * See comments over wake_up_bit() and waitqueue_active().
	 */
	smp_mb();
	wake_up_var(&cookie->stage);
}

/*
 * Change the stage a cookie is at and wake up anyone waiting for that - but
 * only if the cookie isn't already marked as being in a cleanup state.
 */
void fscache_set_cookie_stage(struct fscache_cookie *cookie,
			      enum fscache_cookie_stage stage)
{
	bool changed = false;

	spin_lock(&cookie->lock);
	switch (cookie->stage) {
	case FSCACHE_COOKIE_STAGE_RELINQUISHING:
		break;
	default:
		cookie->stage = stage;
		changed = true;
		break;
	}
	spin_unlock(&cookie->lock);
	if (changed)
		wake_up_cookie_stage(cookie);
}
EXPORT_SYMBOL(fscache_set_cookie_stage);

/*
 * Set the index key in a cookie.  The cookie struct has space for a 16-byte
 * key plus length and hash, but if that's not big enough, it's instead a
 * pointer to a buffer containing 3 bytes of hash, 1 byte of length and then
 * the key data.
 */
static int fscache_set_key(struct fscache_cookie *cookie,
			   const void *index_key, size_t index_key_len)
{
	unsigned long long h;
	u32 *buf;
	int bufs;
	int i;

	bufs = DIV_ROUND_UP(index_key_len, sizeof(*buf));

	if (index_key_len > sizeof(cookie->inline_key)) {
		buf = kcalloc(bufs, sizeof(*buf), GFP_KERNEL);
		if (!buf)
			return -ENOMEM;
		cookie->key = buf;
	} else {
		buf = (u32 *)cookie->inline_key;
	}

	memcpy(buf, index_key, index_key_len);

	/* Calculate a hash and combine this with the length in the first word
	 * or first half word
	 */
	h = (unsigned long)cookie->volume;

	for (i = 0; i < bufs; i++)
		h += buf[i];

	cookie->key_hash = h ^ (h >> 32);
	return 0;
}

static long fscache_compare_cookie(const struct fscache_cookie *a,
				   const struct fscache_cookie *b)
{
	const void *ka, *kb;

	if (a->key_hash != b->key_hash)
		return (long)a->key_hash - (long)b->key_hash;
	if (a->volume != b->volume)
		return (long)a->volume - (long)b->volume;
	if (a->key_len != b->key_len)
		return (long)a->key_len - (long)b->key_len;

	if (a->key_len <= sizeof(a->inline_key)) {
		ka = &a->inline_key;
		kb = &b->inline_key;
	} else {
		ka = a->key;
		kb = b->key;
	}
	return memcmp(ka, kb, a->key_len);
}

static atomic_t fscache_cookie_debug_id = ATOMIC_INIT(1);

/*
 * Allocate a cookie.
 */
static struct fscache_cookie *fscache_alloc_cookie(
	struct fscache_volume *volume,
	u8 advice,
	const void *index_key, size_t index_key_len,
	const void *aux_data, size_t aux_data_len,
	loff_t object_size)
{
	struct fscache_cookie *cookie;

	/* allocate and initialise a cookie */
	cookie = kmem_cache_zalloc(fscache_cookie_jar, GFP_KERNEL);
	if (!cookie)
		return NULL;
	fscache_stat(&fscache_n_cookies);

	cookie->volume		= volume;
	cookie->advice		= advice;
	cookie->key_len		= index_key_len;
	cookie->aux_len		= aux_data_len;
	cookie->object_size	= object_size;
	cookie->zero_point	= object_size;

	if (fscache_set_key(cookie, index_key, index_key_len) < 0)
		goto nomem;

	if (cookie->aux_len <= sizeof(cookie->inline_aux)) {
		memcpy(cookie->inline_aux, aux_data, cookie->aux_len);
	} else {
		cookie->aux = kmemdup(aux_data, cookie->aux_len, GFP_KERNEL);
		if (!cookie->aux)
			goto nomem;
	}

	refcount_set(&cookie->ref, 1);
	cookie->debug_id = atomic_inc_return(&fscache_cookie_debug_id);
	cookie->stage = FSCACHE_COOKIE_STAGE_QUIESCENT;
	spin_lock_init(&cookie->lock);

	write_lock(&fscache_cookies_lock);
	list_add_tail(&cookie->proc_link, &fscache_cookies);
	write_unlock(&fscache_cookies_lock);
	fscache_see_cookie(cookie, fscache_cookie_new_acquire);
	return cookie;

nomem:
	fscache_free_cookie(cookie);
	return NULL;
}

static void fscache_wait_on_collision(struct fscache_cookie *candidate,
				      struct fscache_cookie *wait_for)
{
	enum fscache_cookie_stage *stagep = &wait_for->stage;

	wait_var_event_timeout(stagep, READ_ONCE(*stagep) == FSCACHE_COOKIE_STAGE_DROPPED,
			       20 * HZ);
	if (READ_ONCE(*stagep) != FSCACHE_COOKIE_STAGE_DROPPED) {
		pr_notice("Potential collision c=%08x old: c=%08x",
			  candidate->debug_id, wait_for->debug_id);
		wait_var_event(stagep, READ_ONCE(*stagep) == FSCACHE_COOKIE_STAGE_DROPPED);
	}
}

/*
 * Attempt to insert the new cookie into the hash.  If there's a collision, we
 * wait for the old cookie to complete if it's being relinquished and an error
 * otherwise.
 */
static bool fscache_hash_cookie(struct fscache_cookie *candidate)
{
	struct fscache_cookie *cursor, *wait_for = NULL;
	struct hlist_bl_head *h;
	struct hlist_bl_node *p;
	unsigned int bucket;

	bucket = candidate->key_hash & (ARRAY_SIZE(fscache_cookie_hash) - 1);
	h = &fscache_cookie_hash[bucket];

	hlist_bl_lock(h);
	hlist_bl_for_each_entry(cursor, p, h, hash_link) {
		if (fscache_compare_cookie(candidate, cursor) == 0) {
			if (!test_bit(FSCACHE_COOKIE_RELINQUISHED, &cursor->flags))
				goto collision;
			wait_for = fscache_get_cookie(cursor,
						      fscache_cookie_get_hash_collision);
			break;
		}
	}

	fscache_get_volume(candidate->volume, fscache_volume_get_cookie);
	atomic_inc(&candidate->volume->n_cookies);
	hlist_bl_add_head(&candidate->hash_link, h);
	hlist_bl_unlock(h);

	if (wait_for) {
		fscache_wait_on_collision(candidate, wait_for);
		fscache_put_cookie(wait_for, fscache_cookie_put_hash_collision);
	}
	return true;

collision:
	trace_fscache_cookie(cursor->debug_id, refcount_read(&cursor->ref),
			     fscache_cookie_collision);
	pr_err("Duplicate cookie detected\n");
	fscache_print_cookie(cursor, 'O');
	fscache_print_cookie(candidate, 'N');
	hlist_bl_unlock(h);
	return false;
}

/*
 * Request a cookie to represent a data storage object within a volume.
 *
 * We never let on to the netfs about errors.  We may set a negative cookie
 * pointer, but that's okay
 */
struct fscache_cookie *__fscache_acquire_cookie(
	struct fscache_volume *volume,
	u8 advice,
	const void *index_key, size_t index_key_len,
	const void *aux_data, size_t aux_data_len,
	loff_t object_size)
{
	struct fscache_cookie *cookie;

	_enter("V=%x", volume->debug_id);

	if (!index_key || !index_key_len || index_key_len > 255 || aux_data_len > 255)
		return NULL;
	if (!aux_data || !aux_data_len) {
		aux_data = NULL;
		aux_data_len = 0;
	}

	fscache_stat(&fscache_n_acquires);

	cookie = fscache_alloc_cookie(volume, advice,
				      index_key, index_key_len,
				      aux_data, aux_data_len,
				      object_size);
	if (!cookie) {
		fscache_stat(&fscache_n_acquires_oom);
		return NULL;
	}

	if (!fscache_hash_cookie(cookie)) {
		fscache_see_cookie(cookie, fscache_cookie_discard);
		fscache_free_cookie(cookie);
		return NULL;
	}

	trace_fscache_acquire(cookie);
	fscache_stat(&fscache_n_acquires_ok);
	_leave(" = c=%08x", cookie->debug_id);
	return cookie;
}
EXPORT_SYMBOL(__fscache_acquire_cookie);

/*
 * Prepare a cache object to be written to.
 */
static void fscache_prepare_to_write(struct fscache_cookie *cookie, int param)
{
	cookie->volume->cache->ops->prepare_to_write(cookie);
}

/*
 * Look up a cookie to the cache.
 */
static void fscache_lookup_cookie(struct fscache_cookie *cookie, int param)
{
	bool will_modify = param;

	_enter("");

	if (!cookie->volume->cache->ops->lookup_cookie(cookie)) {
		if (cookie->stage != FSCACHE_COOKIE_STAGE_FAILED)
			fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_QUIESCENT);
		_leave(" [fail]");
		goto out;
	}

	if (will_modify &&
	    test_and_set_bit(FSCACHE_COOKIE_LOCAL_WRITE, &cookie->flags))
		fscache_prepare_to_write(cookie, 0);

	fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_ACTIVE);

out:
	fscache_end_volume_access(cookie->volume, fscache_access_lookup_cookie_end);
	fscache_end_cookie_access(cookie, fscache_access_lookup_cookie_end);
}

/*
 * Start using the cookie for I/O.  This prevents the backing object from being
 * reaped by VM pressure.
 */
void __fscache_use_cookie(struct fscache_cookie *cookie, bool will_modify)
{
	enum fscache_cookie_stage stage;
	bool do_look_up = false, write_set;

	_enter("c=%08x", cookie->debug_id);

	if (WARN(test_bit(FSCACHE_COOKIE_RELINQUISHED, &cookie->flags),
		 "Trying to use relinquished cookie\n"))
		return;

	spin_lock(&cookie->lock);

	atomic_inc(&cookie->n_active);

again:
	stage = cookie->stage;
	switch (stage) {
	case FSCACHE_COOKIE_STAGE_QUIESCENT:
		if (fscache_begin_volume_access(cookie->volume,
						fscache_access_lookup_cookie)) {
			__fscache_begin_cookie_access(cookie,
						      fscache_access_lookup_cookie);
			cookie->stage = FSCACHE_COOKIE_STAGE_LOOKING_UP;
			smp_mb__before_atomic(); /* Set stage before is-caching
						  * vs __fscache_begin_cookie_access()
						  */
			set_bit(FSCACHE_COOKIE_IS_CACHING, &cookie->flags);
			do_look_up = true;
		}

		spin_unlock(&cookie->lock);
		wake_up_cookie_stage(cookie);
		if (do_look_up)
			fscache_dispatch(cookie, will_modify, fscache_lookup_cookie);
		break;

	case FSCACHE_COOKIE_STAGE_LOOKING_UP:
		spin_unlock(&cookie->lock);
		wait_var_event(&cookie->stage, READ_ONCE(cookie->stage) != stage);
		spin_lock(&cookie->lock);
		goto again;

	case FSCACHE_COOKIE_STAGE_ACTIVE:
	case FSCACHE_COOKIE_STAGE_INVALIDATING:
		if (will_modify) {
			write_set = test_and_set_bit(FSCACHE_COOKIE_LOCAL_WRITE,
						     &cookie->flags);
			spin_unlock(&cookie->lock);
			if (!write_set)
				fscache_dispatch(cookie, 0, fscache_prepare_to_write);
		} else {
			spin_unlock(&cookie->lock);
		}
		break;

	case FSCACHE_COOKIE_STAGE_FAILED:
		spin_unlock(&cookie->lock);
		break;

	case FSCACHE_COOKIE_STAGE_DROPPED:
	case FSCACHE_COOKIE_STAGE_RELINQUISHING:
		spin_unlock(&cookie->lock);
		WARN(1, "Can't use cookie in stage %u\n", cookie->stage);
		break;
	}

	_leave("");
}
EXPORT_SYMBOL(__fscache_use_cookie);

/*
 * Stop using the cookie for I/O.
 */
void __fscache_unuse_cookie(struct fscache_cookie *cookie,
			    const void *aux_data, const loff_t *object_size)
{
	if (aux_data || object_size)
		__fscache_update_cookie(cookie, aux_data, object_size);
	if (atomic_dec_and_test(&cookie->n_active))
		clear_bit(FSCACHE_COOKIE_DISABLED, &cookie->flags);
}
EXPORT_SYMBOL(__fscache_unuse_cookie);

/*
 * Ask the cache to effect invalidation of a cookie.
 */
static void fscache_invalidate_cookie(struct fscache_cookie *cookie, int flags)
{
	set_bit(FSCACHE_COOKIE_NO_DATA_TO_READ, &cookie->flags);
	if (cookie->volume->cache->ops->invalidate_cookie(cookie, flags))
		fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_ACTIVE);
	else
		fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_FAILED);
	fscache_end_cookie_access(cookie, fscache_access_invalidate_cookie_end);
}

/*
 * Invalidate an object.
 */
void __fscache_invalidate(struct fscache_cookie *cookie,
			  const void *aux_data, loff_t new_size,
			  unsigned int flags)
{
	bool is_caching;

	_enter("c=%x", cookie->debug_id);

	fscache_stat(&fscache_n_invalidates);

	if (WARN(test_bit(FSCACHE_COOKIE_RELINQUISHED, &cookie->flags),
		 "Trying to invalidate relinquished cookie\n"))
		return;

	if ((flags & FSCACHE_INVAL_DIO_WRITE) &&
	    test_and_set_bit(FSCACHE_COOKIE_DISABLED, &cookie->flags))
		return;

	spin_lock(&cookie->lock);
	fscache_update_aux(cookie, aux_data, &new_size);
	cookie->zero_point = new_size;
	cookie->inval_counter++;

	trace_fscache_invalidate(cookie, new_size);

	switch (cookie->stage) {
	case FSCACHE_COOKIE_STAGE_INVALIDATING: /* is_still_valid will catch it */
	default:
		spin_unlock(&cookie->lock);
		_leave(" [no %u]", cookie->stage);
		return;

	case FSCACHE_COOKIE_STAGE_LOOKING_UP:
		spin_unlock(&cookie->lock);
		_leave(" [look %x]", cookie->inval_counter);
		return;

	case FSCACHE_COOKIE_STAGE_ACTIVE:
		cookie->stage = FSCACHE_COOKIE_STAGE_INVALIDATING;
		is_caching = fscache_begin_cookie_access(
			cookie, fscache_access_invalidate_cookie);
		spin_unlock(&cookie->lock);
		wake_up_cookie_stage(cookie);

		if (is_caching)
			fscache_dispatch(cookie, flags, fscache_invalidate_cookie);
		_leave(" [inv]");
		return;
	}
}
EXPORT_SYMBOL(__fscache_invalidate);

/*
 * Remove a cookie from the hash table.
 */
static void fscache_unhash_cookie(struct fscache_cookie *cookie)
{
	struct hlist_bl_head *h;
	unsigned int bucket;

	bucket = cookie->key_hash & (ARRAY_SIZE(fscache_cookie_hash) - 1);
	h = &fscache_cookie_hash[bucket];

	hlist_bl_lock(h);
	hlist_bl_del(&cookie->hash_link);
	hlist_bl_unlock(h);
}

/*
 * Finalise a cookie after all its resources have been disposed of.
 */
void fscache_drop_cookie(struct fscache_cookie *cookie,
			 enum fscache_cookie_trace where)
{
	spin_lock(&cookie->lock);
	cookie->stage = FSCACHE_COOKIE_STAGE_DROPPED;
	spin_unlock(&cookie->lock);
	wake_up_cookie_stage(cookie);

	fscache_unhash_cookie(cookie);
	fscache_stat(&fscache_n_relinquishes_dropped);
	fscache_put_cookie(cookie, where);
}
EXPORT_SYMBOL(fscache_drop_cookie);

/*
 * Tell the cache that we're relinquishing a cookie.
 */
static void fscache_do_relinquish_cookie(struct fscache_cookie *cookie, int param)
{
	_enter("c=%08x", cookie->debug_id);

	fscache_see_cookie(cookie, fscache_cookie_see_relinquish);
	cookie->volume->cache->ops->relinquish_cookie(cookie);
	fscache_end_cookie_access(cookie, fscache_access_relinquish_cookie_end);
}

/*
 * Allow the netfs to release a cookie back to the cache.
 * - the object will be marked as recyclable on disk if retire is true
 */
void __fscache_relinquish_cookie(struct fscache_cookie *cookie, bool retire)
{
	fscache_stat(&fscache_n_relinquishes);
	if (retire)
		fscache_stat(&fscache_n_relinquishes_retire);

	_enter("c=%08x{%d},%d",
	       cookie->debug_id, atomic_read(&cookie->n_active), retire);

	if (WARN(test_and_set_bit(FSCACHE_COOKIE_RELINQUISHED, &cookie->flags),
		 "Cookie c=%x already relinquished\n", cookie->debug_id))
		return;

	if (retire)
		set_bit(FSCACHE_COOKIE_RETIRED, &cookie->flags);
	trace_fscache_relinquish(cookie, retire);

	ASSERTCMP(atomic_read(&cookie->n_active), ==, 0);
	ASSERTCMP(atomic_read(&cookie->volume->n_cookies), >, 0);
	atomic_dec(&cookie->volume->n_cookies);

	fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_RELINQUISHING);

	if (fscache_begin_cookie_access(cookie, fscache_access_relinquish_cookie))
		fscache_dispatch(cookie, 0, fscache_do_relinquish_cookie);
	else
		fscache_drop_cookie(cookie, fscache_cookie_put_relinquish);
}
EXPORT_SYMBOL(__fscache_relinquish_cookie);

/*
 * Drop a reference to a cookie.
 */
void fscache_put_cookie(struct fscache_cookie *cookie,
			enum fscache_cookie_trace where)
{
	struct fscache_volume *volume = cookie->volume;
	unsigned int cookie_debug_id = cookie->debug_id;
	bool zero;
	int ref;

	zero = __refcount_dec_and_test(&cookie->ref, &ref);
	trace_fscache_cookie(cookie_debug_id, ref - 1, where);
	if (zero) {
		fscache_free_cookie(cookie);
		fscache_put_volume(volume, fscache_volume_put_cookie);
	}
}
EXPORT_SYMBOL(fscache_put_cookie);

/*
 * Get a reference to a cookie.
 */
struct fscache_cookie *fscache_get_cookie(struct fscache_cookie *cookie,
					  enum fscache_cookie_trace where)
{
	int ref;

	__refcount_inc(&cookie->ref, &ref);
	trace_fscache_cookie(cookie->debug_id, ref + 1, where);
	return cookie;
}
EXPORT_SYMBOL(fscache_get_cookie);

/*
 * Generate a list of extant cookies in /proc/fs/fscache/cookies
 */
static int fscache_cookies_seq_show(struct seq_file *m, void *v)
{
	struct fscache_cookie *cookie;
	unsigned int keylen = 0, auxlen = 0;
	u8 *p;

	if (v == &fscache_cookies) {
		seq_puts(m,
			 "COOKIE   PARENT   USE ACT ACC S FL DEF             \n"
			 "======== ======== === === === = == ================\n"
			 );
		return 0;
	}

	cookie = list_entry(v, struct fscache_cookie, proc_link);

	seq_printf(m,
		   "%08x %08x %3d %3d %3d %c %02lx",
		   cookie->debug_id,
		   cookie->volume->debug_id,
		   refcount_read(&cookie->ref),
		   atomic_read(&cookie->n_active),
		   atomic_read(&cookie->n_accesses) - 1,
		   fscache_cookie_stages[cookie->stage],
		   cookie->flags);

	keylen = cookie->key_len;
	auxlen = cookie->aux_len;

	if (keylen > 0 || auxlen > 0) {
		seq_puts(m, " ");
		p = keylen <= sizeof(cookie->inline_key) ?
			cookie->inline_key : cookie->key;
		for (; keylen > 0; keylen--)
			seq_printf(m, "%02x", *p++);
		if (auxlen > 0) {
			seq_puts(m, ", ");
			p = auxlen <= sizeof(cookie->inline_aux) ?
				cookie->inline_aux : cookie->aux;
			for (; auxlen > 0; auxlen--)
				seq_printf(m, "%02x", *p++);
		}
	}

	seq_puts(m, "\n");
	return 0;
}

static void *fscache_cookies_seq_start(struct seq_file *m, loff_t *_pos)
	__acquires(fscache_cookies_lock)
{
	read_lock(&fscache_cookies_lock);
	return seq_list_start_head(&fscache_cookies, *_pos);
}

static void *fscache_cookies_seq_next(struct seq_file *m, void *v, loff_t *_pos)
{
	return seq_list_next(v, &fscache_cookies, _pos);
}

static void fscache_cookies_seq_stop(struct seq_file *m, void *v)
	__releases(rcu)
{
	read_unlock(&fscache_cookies_lock);
}


const struct seq_operations fscache_cookies_seq_ops = {
	.start  = fscache_cookies_seq_start,
	.next   = fscache_cookies_seq_next,
	.stop   = fscache_cookies_seq_stop,
	.show   = fscache_cookies_seq_show,
};
