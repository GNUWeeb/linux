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

static void fscache_cookie_lru_timed_out(struct timer_list *timer);
static void fscache_cookie_lru_worker(struct work_struct *work);
static void fscache_cookie_worker(struct work_struct *work);
static void fscache_drop_cookie(struct fscache_cookie *cookie);
static void fscache_lookup_cookie(struct fscache_cookie *cookie);
static void fscache_invalidate_cookie(struct fscache_cookie *cookie);

#define fscache_cookie_hash_shift 15
static struct hlist_bl_head fscache_cookie_hash[1 << fscache_cookie_hash_shift];
static LIST_HEAD(fscache_cookies);
static DEFINE_RWLOCK(fscache_cookies_lock);
static LIST_HEAD(fscache_cookie_lru);
static DEFINE_SPINLOCK(fscache_cookie_lru_lock);
DEFINE_TIMER(fscache_cookie_lru_timer, fscache_cookie_lru_timed_out);
static DECLARE_WORK(fscache_cookie_lru_work, fscache_cookie_lru_worker);
static const char fscache_cookie_stages[FSCACHE_COOKIE_STAGE__NR] = "-LCAIFMWRD";
unsigned int fscache_lru_cookie_timeout = 10 * HZ;

void fscache_print_cookie(struct fscache_cookie *cookie, char prefix)
{
	const u8 *k;

	pr_err("%c-cookie c=%08x [fl=%lx na=%u nA=%u s=%c]\n",
	       prefix,
	       cookie->debug_id,
	       cookie->flags,
	       atomic_read(&cookie->n_active),
	       atomic_read(&cookie->n_accesses),
	       fscache_cookie_stages[cookie->stage]);
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
	if (WARN_ON_ONCE(!list_empty(&cookie->commit_link))) {
		spin_lock(&fscache_cookie_lru_lock);
		list_del_init(&cookie->commit_link);
		spin_unlock(&fscache_cookie_lru_lock);
		fscache_stat_d(&fscache_n_cookies_lru);
		fscache_stat(&fscache_n_cookies_lru_removed);
	}
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

static void __fscache_queue_cookie(struct fscache_cookie *cookie)
{
	if (!queue_work(fscache_wq, &cookie->work))
		fscache_put_cookie(cookie, fscache_cookie_put_over_queued);
}

static void fscache_queue_cookie(struct fscache_cookie *cookie,
				 enum fscache_cookie_trace where)
{
	fscache_get_cookie(cookie, where);
	__fscache_queue_cookie(cookie);
}

static void __fscache_end_cookie_access(struct fscache_cookie *cookie)
{
	if (test_bit(FSCACHE_COOKIE_DO_RELINQUISH, &cookie->flags))
		fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_RELINQUISHING);
	else if (test_bit(FSCACHE_COOKIE_DO_WITHDRAW, &cookie->flags))
		fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_WITHDRAWING);
	fscache_queue_cookie(cookie, fscache_cookie_get_end_access);
}

/*
 * Mark the end of an access on a cookie.  This brings a deferred
 * relinquishment or withdrawal stage into effect.
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
		__fscache_end_cookie_access(cookie);
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

static void __fscache_set_cookie_stage(struct fscache_cookie *cookie,
				       enum fscache_cookie_stage stage)
{
	cookie->stage = stage;
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
		__fscache_set_cookie_stage(cookie, stage);
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
	u32 *buf;
	int bufs;

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
	cookie->key_hash = fscache_hash(cookie->volume->key_hash, buf, bufs);
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
	INIT_LIST_HEAD(&cookie->commit_link);
	INIT_WORK(&cookie->work, fscache_cookie_worker);

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
 * Look up a cookie to the cache.
 */
static void fscache_lookup_cookie(struct fscache_cookie *cookie)
{
	bool changed_stage = false, need_withdraw = false;

	_enter("");

	if (!cookie->volume->cache_priv) {
		fscache_create_volume(cookie->volume, true);
		if (!cookie->volume->cache_priv) {
			fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_QUIESCENT);
			goto out;
		}
	}

	if (!cookie->volume->cache->ops->lookup_cookie(cookie)) {
		if (cookie->stage != FSCACHE_COOKIE_STAGE_FAILED)
			fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_QUIESCENT);
		need_withdraw = true;
		_leave(" [fail]");
		goto out;
	}

	spin_lock(&cookie->lock);
	if (cookie->stage != FSCACHE_COOKIE_STAGE_RELINQUISHING) {
		__fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_ACTIVE);
		fscache_see_cookie(cookie, fscache_cookie_see_active);
		changed_stage = true;
	}
	spin_unlock(&cookie->lock);
	if (changed_stage)
		wake_up_cookie_stage(cookie);

out:
	fscache_end_cookie_access(cookie, fscache_access_lookup_cookie_end);
	if (need_withdraw)
		cookie->volume->cache->ops->withdraw_cookie(cookie);
	fscache_end_volume_access(cookie->volume, fscache_access_lookup_cookie_end);
}

/*
 * Start using the cookie for I/O.  This prevents the backing object from being
 * reaped by VM pressure.
 */
void __fscache_use_cookie(struct fscache_cookie *cookie, bool will_modify)
{
	enum fscache_cookie_stage stage;
	bool changed_stage = false, queue = false;

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
		if (!fscache_begin_volume_access(cookie->volume,
						 fscache_access_lookup_cookie))
			break;

		__fscache_begin_cookie_access(cookie, fscache_access_lookup_cookie);
		__fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_LOOKING_UP);
		smp_mb__before_atomic(); /* Set stage before is-caching
					  * vs __fscache_begin_cookie_access()
					  */
		set_bit(FSCACHE_COOKIE_IS_CACHING, &cookie->flags);
		set_bit(FSCACHE_COOKIE_HAS_BEEN_CACHED, &cookie->flags);
		changed_stage = true;
		queue = true;
		break;

	case FSCACHE_COOKIE_STAGE_LOOKING_UP:
	case FSCACHE_COOKIE_STAGE_CREATING:
	case FSCACHE_COOKIE_STAGE_ACTIVE:
	case FSCACHE_COOKIE_STAGE_INVALIDATING:
	case FSCACHE_COOKIE_STAGE_FAILED:
	case FSCACHE_COOKIE_STAGE_WITHDRAWING:
		break;

	case FSCACHE_COOKIE_STAGE_COMMITTING:
		spin_unlock(&cookie->lock);
		wait_var_event(&cookie->stage,
			       READ_ONCE(cookie->stage) != FSCACHE_COOKIE_STAGE_COMMITTING);
		spin_lock(&cookie->lock);
		goto again;

	case FSCACHE_COOKIE_STAGE_DROPPED:
	case FSCACHE_COOKIE_STAGE_RELINQUISHING:
		WARN(1, "Can't use cookie in stage %u\n", cookie->stage);
		break;
	}

	spin_unlock(&cookie->lock);
	if (changed_stage)
		wake_up_cookie_stage(cookie);
	if (queue)
		fscache_queue_cookie(cookie, fscache_cookie_get_use_work);
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
	cookie->unused_at = jiffies;
	if (atomic_dec_return(&cookie->n_active) == 0) {
		if (test_bit(FSCACHE_COOKIE_IS_CACHING, &cookie->flags)) {
			spin_lock(&fscache_cookie_lru_lock);
			if (list_empty(&cookie->commit_link)) {
				fscache_get_cookie(cookie, fscache_cookie_get_lru);
				list_move_tail(&cookie->commit_link, &fscache_cookie_lru);
				fscache_stat(&fscache_n_cookies_lru);
			}
			spin_unlock(&fscache_cookie_lru_lock);
			timer_reduce(&fscache_cookie_lru_timer,
				     jiffies + fscache_lru_cookie_timeout);
		}
	}
}
EXPORT_SYMBOL(__fscache_unuse_cookie);

/*
 * Perform work upon the cookie, such as committing its cache state,
 * relinquishing it or withdrawing the backing cache.  We're protected from the
 * cache going away under us as object withdrawal must come through this
 * non-reentrant work item.
 */
static void __fscache_cookie_worker(struct fscache_cookie *cookie)
{
	_enter("c=%x", cookie->debug_id);

again:
	switch (READ_ONCE(cookie->stage)) {
	case FSCACHE_COOKIE_STAGE_ACTIVE:
		break;

	case FSCACHE_COOKIE_STAGE_LOOKING_UP:
		fscache_lookup_cookie(cookie);
		goto again;

	case FSCACHE_COOKIE_STAGE_CREATING:
		WARN_ONCE(1, "Cookie %x in unexpected stage %u\n",
			  cookie->debug_id, cookie->stage);
		break;

	case FSCACHE_COOKIE_STAGE_INVALIDATING:
		fscache_invalidate_cookie(cookie);
		goto again;

	case FSCACHE_COOKIE_STAGE_FAILED:
		break;

	case FSCACHE_COOKIE_STAGE_COMMITTING:
	case FSCACHE_COOKIE_STAGE_RELINQUISHING:
	case FSCACHE_COOKIE_STAGE_WITHDRAWING:
		if (test_and_clear_bit(FSCACHE_COOKIE_IS_CACHING, &cookie->flags) &&
		    cookie->cache_priv)
			cookie->volume->cache->ops->withdraw_cookie(cookie);
		if (cookie->stage == FSCACHE_COOKIE_STAGE_RELINQUISHING) {
			fscache_see_cookie(cookie, fscache_cookie_see_relinquish);
			fscache_drop_cookie(cookie);
			break;
		} else if (cookie->stage == FSCACHE_COOKIE_STAGE_COMMITTING) {
			fscache_see_cookie(cookie, fscache_cookie_see_committing);
		} else {
			fscache_see_cookie(cookie, fscache_cookie_see_withdraw);
		}
		fallthrough;

	case FSCACHE_COOKIE_STAGE_QUIESCENT:
	case FSCACHE_COOKIE_STAGE_DROPPED:
		clear_bit(FSCACHE_COOKIE_NEEDS_UPDATE, &cookie->flags);
		clear_bit(FSCACHE_COOKIE_DO_WITHDRAW, &cookie->flags);
		clear_bit(FSCACHE_COOKIE_DO_COMMIT, &cookie->flags);
		set_bit(FSCACHE_COOKIE_NO_DATA_TO_READ, &cookie->flags);
		fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_QUIESCENT);
		break;
	}
	_leave("");
}

static void fscache_cookie_worker(struct work_struct *work)
{
	struct fscache_cookie *cookie = container_of(work, struct fscache_cookie, work);

	fscache_see_cookie(cookie, fscache_cookie_see_work);
	__fscache_cookie_worker(cookie);
	fscache_put_cookie(cookie, fscache_cookie_put_work);
}

/*
 * Wait for the object to become inactive.  The cookie's work item will be
 * scheduled when someone transitions n_accesses to 0.
 */
static void __fscache_withdraw_cookie(struct fscache_cookie *cookie)
{
	if (test_and_clear_bit(FSCACHE_COOKIE_NACC_ELEVATED, &cookie->flags))
		fscache_end_cookie_access(cookie, fscache_access_cache_unpin);
	else
		__fscache_end_cookie_access(cookie);
}

static void fscache_cookie_lru_do_one(struct fscache_cookie *cookie)
{
	fscache_see_cookie(cookie, fscache_cookie_see_lru_do_one);

	spin_lock(&cookie->lock);
	if (cookie->stage != FSCACHE_COOKIE_STAGE_ACTIVE ||
	    time_before(jiffies, cookie->unused_at + fscache_lru_cookie_timeout) ||
	    atomic_read(&cookie->n_active) > 0) {
		spin_unlock(&cookie->lock);
		fscache_stat(&fscache_n_cookies_lru_removed);
	} else {
		__fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_COMMITTING);
		set_bit(FSCACHE_COOKIE_DO_COMMIT, &cookie->flags);
		spin_unlock(&cookie->lock);
		fscache_stat(&fscache_n_cookies_lru_expired);
		_debug("lru c=%x", cookie->debug_id);
		__fscache_withdraw_cookie(cookie);
	}

	fscache_put_cookie(cookie, fscache_cookie_put_lru);
}

static void fscache_cookie_lru_worker(struct work_struct *work)
{
	struct fscache_cookie *cookie;
	unsigned long unused_at;

	spin_lock(&fscache_cookie_lru_lock);

	while (!list_empty(&fscache_cookie_lru)) {
		cookie = list_first_entry(&fscache_cookie_lru,
					  struct fscache_cookie, commit_link);
		unused_at = cookie->unused_at + fscache_lru_cookie_timeout;
		if (time_before(jiffies, unused_at)) {
			timer_reduce(&fscache_cookie_lru_timer, unused_at);
			break;
		}

		list_del_init(&cookie->commit_link);
		fscache_stat_d(&fscache_n_cookies_lru);
		spin_unlock(&fscache_cookie_lru_lock);
		fscache_cookie_lru_do_one(cookie);
		spin_lock(&fscache_cookie_lru_lock);
	}

	spin_unlock(&fscache_cookie_lru_lock);
}

static void fscache_cookie_lru_timed_out(struct timer_list *timer)
{
	queue_work(fscache_wq, &fscache_cookie_lru_work);
}

static void fscache_cookie_drop_from_lru(struct fscache_cookie *cookie)
{
	bool need_put = false;

	if (!list_empty(&cookie->commit_link)) {
		spin_lock(&fscache_cookie_lru_lock);
		if (!list_empty(&cookie->commit_link)) {
			list_del_init(&cookie->commit_link);
			fscache_stat_d(&fscache_n_cookies_lru);
			fscache_stat(&fscache_n_cookies_lru_dropped);
			need_put = true;
		}
		spin_unlock(&fscache_cookie_lru_lock);
		if (need_put)
			fscache_put_cookie(cookie, fscache_cookie_put_lru);
	}
}

/*
 * Ask the cache to effect invalidation of a cookie.
 */
static void fscache_invalidate_cookie(struct fscache_cookie *cookie)
{
	if (cookie->volume->cache->ops->invalidate_cookie(cookie, 0))
		fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_ACTIVE);
	else
		fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_FAILED);
	fscache_end_cookie_access(cookie, fscache_access_invalidate_cookie_end);
}

/*
 * Invalidate an object.  Callable with spinlocks held.
 */
void __fscache_invalidate(struct fscache_cookie *cookie)
{
	bool is_caching;

	_enter("c=%x", cookie->debug_id);

	fscache_stat(&fscache_n_invalidates);

	if (WARN(test_bit(FSCACHE_COOKIE_RELINQUISHED, &cookie->flags),
		 "Trying to invalidate relinquished cookie\n"))
		return;

	spin_lock(&cookie->lock);
	set_bit(FSCACHE_COOKIE_NO_DATA_TO_READ, &cookie->flags);
	cookie->inval_counter++;

	switch (cookie->stage) {
	case FSCACHE_COOKIE_STAGE_INVALIDATING: /* is_still_valid will catch it */
	default:
		spin_unlock(&cookie->lock);
		_leave(" [no %u]", cookie->stage);
		return;

	case FSCACHE_COOKIE_STAGE_LOOKING_UP:
	case FSCACHE_COOKIE_STAGE_CREATING:
		spin_unlock(&cookie->lock);
		_leave(" [look %x]", cookie->inval_counter);
		return;

	case FSCACHE_COOKIE_STAGE_ACTIVE:
		__fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_INVALIDATING);
		is_caching = fscache_begin_cookie_access(
			cookie, fscache_access_invalidate_cookie);
		spin_unlock(&cookie->lock);
		wake_up_cookie_stage(cookie);

		if (is_caching)
			fscache_queue_cookie(cookie, fscache_cookie_get_inval_work);
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
static void fscache_drop_cookie(struct fscache_cookie *cookie)
{
	spin_lock(&cookie->lock);
	__fscache_set_cookie_stage(cookie, FSCACHE_COOKIE_STAGE_DROPPED);
	spin_unlock(&cookie->lock);
	wake_up_cookie_stage(cookie);

	fscache_unhash_cookie(cookie);
	fscache_stat(&fscache_n_relinquishes_dropped);
}

static void fscache_drop_withdraw_cookie(struct fscache_cookie *cookie)
{
	fscache_cookie_drop_from_lru(cookie);
	__fscache_withdraw_cookie(cookie);
}

/**
 * fscache_withdraw_cookie - Mark a cookie for withdrawal
 * @cookie: The cookie to be withdrawn.
 *
 * Allow the cache backend to withdraw the backing for a cookie for its own
 * reasons, even if that cookie is in active use.
 */
void fscache_withdraw_cookie(struct fscache_cookie *cookie)
{
	set_bit(FSCACHE_COOKIE_DO_WITHDRAW, &cookie->flags);
	fscache_drop_withdraw_cookie(cookie);
}
EXPORT_SYMBOL(fscache_withdraw_cookie);

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

	set_bit(FSCACHE_COOKIE_DO_RELINQUISH, &cookie->flags);

	if (test_bit(FSCACHE_COOKIE_HAS_BEEN_CACHED, &cookie->flags))
		fscache_drop_withdraw_cookie(cookie);
	else
		fscache_drop_cookie(cookie);
	fscache_put_cookie(cookie, fscache_cookie_put_relinquish);
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
			 "COOKIE   VOLUME   REF ACT ACC S FL DEF             \n"
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
