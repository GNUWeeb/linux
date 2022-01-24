/* SPDX-License-Identifier: GPL-2.0-or-later */
/* Internal definitions for network filesystem support
 *
 * Copyright (C) 2021 Red Hat, Inc. All Rights Reserved.
 * Written by David Howells (dhowells@redhat.com)
 */

#include <linux/netfs.h>
#include <linux/fscache.h>
#include <trace/events/netfs.h>

#ifdef pr_fmt
#undef pr_fmt
#endif

#define pr_fmt(fmt) "netfs: " fmt

/*
 * dio_helper.c
 */
ssize_t netfs_file_direct_write(struct netfs_dirty_region *region,
				struct kiocb *iocb, struct iov_iter *from);

/*
 * main.c
 */
extern struct list_head netfs_regions;
extern spinlock_t netfs_regions_lock;

#ifdef CONFIG_PROC_FS
static inline void netfs_proc_add_region(struct netfs_dirty_region *region)
{
	spin_lock(&netfs_regions_lock);
	list_add_tail_rcu(&region->proc_link, &netfs_regions);
	spin_unlock(&netfs_regions_lock);
}
static inline void netfs_proc_del_region(struct netfs_dirty_region *region)
{
	spin_lock(&netfs_regions_lock);
	list_del_rcu(&region->proc_link);
	spin_unlock(&netfs_regions_lock);
}
#else
static inline void netfs_proc_add_region(struct netfs_dirty_region *region) {}
static inline void netfs_proc_del_region(struct netfs_dirty_region *region) {}
#endif

int netfs_sanity_check_ictx(struct address_space *mapping);

/*
 * objects.c
 */
struct netfs_flush_group *netfs_get_flush_group(struct netfs_flush_group *group);
void netfs_put_flush_group(struct netfs_i_context *ctx, struct netfs_flush_group *group);
struct netfs_dirty_region *netfs_alloc_dirty_region(void);
struct netfs_dirty_region *netfs_get_dirty_region(struct netfs_i_context *ctx,
						  struct netfs_dirty_region *region,
						  enum netfs_region_trace what);
void netfs_free_dirty_region(struct netfs_i_context *ctx, struct netfs_dirty_region *region);
void netfs_put_dirty_region(struct netfs_i_context *ctx,
			    struct netfs_dirty_region *region,
			    enum netfs_region_trace what);

/*
 * read_helper.c
 */
extern unsigned int netfs_debug;

struct netfs_read_request *netfs_alloc_read_request(struct address_space *mapping,
						    struct file *file,
						    loff_t start, size_t len,
						    struct netfs_dirty_region *for_write,
						    enum netfs_read_origin origin);
struct netfs_read_subrequest *netfs_alloc_subrequest(struct netfs_read_request *rreq);
void __netfs_put_subrequest(struct netfs_read_subrequest *subreq, bool was_async);
void netfs_get_read_request(struct netfs_read_request *rreq);
void netfs_put_read_request(struct netfs_read_request *rreq, bool was_async);
void netfs_rreq_completed(struct netfs_read_request *rreq, bool was_async);
void netfs_rreq_assess(struct netfs_read_request *rreq, bool was_async);
int netfs_prefetch_for_write(struct file *file, struct folio *folio,
			     struct netfs_dirty_region *region, size_t len);

static inline void netfs_put_subrequest(struct netfs_read_subrequest *subreq,
					bool was_async)
{
	if (refcount_dec_and_test(&subreq->usage))
		__netfs_put_subrequest(subreq, was_async);
}

/*
 * write_helper.c
 */
extern atomic_t netfs_region_debug_ids;

void netfs_flush_region(struct netfs_i_context *ctx,
			struct netfs_dirty_region *region,
			enum netfs_dirty_trace why);

/*
 * stats.c
 */
#ifdef CONFIG_NETFS_STATS
extern atomic_t netfs_n_rh_dio_read;
extern atomic_t netfs_n_rh_readahead;
extern atomic_t netfs_n_rh_readpage;
extern atomic_t netfs_n_rh_rreq;
extern atomic_t netfs_n_rh_sreq;
extern atomic_t netfs_n_rh_download;
extern atomic_t netfs_n_rh_download_done;
extern atomic_t netfs_n_rh_download_failed;
extern atomic_t netfs_n_rh_download_instead;
extern atomic_t netfs_n_rh_read;
extern atomic_t netfs_n_rh_read_done;
extern atomic_t netfs_n_rh_read_failed;
extern atomic_t netfs_n_rh_zero;
extern atomic_t netfs_n_rh_short_read;
extern atomic_t netfs_n_rh_write;
extern atomic_t netfs_n_rh_write_begin;
extern atomic_t netfs_n_rh_write_done;
extern atomic_t netfs_n_rh_write_failed;
extern atomic_t netfs_n_rh_write_zskip;
extern atomic_t netfs_n_wh_region;
extern atomic_t netfs_n_wh_flush_group;


static inline void netfs_stat(atomic_t *stat)
{
	atomic_inc(stat);
}

static inline void netfs_stat_d(atomic_t *stat)
{
	atomic_dec(stat);
}

#else
#define netfs_stat(x) do {} while(0)
#define netfs_stat_d(x) do {} while(0)
#endif

/*
 * Miscellaneous functions.
 */
static inline bool netfs_is_cache_enabled(struct netfs_i_context *ctx)
{
#ifdef CONFIG_FSCACHE
	struct fscache_cookie *cookie = ctx->cache;

	return fscache_cookie_valid(cookie) && fscache_cookie_enabled(cookie);
#else
	return false;
#endif
}

/*****************************************************************************/
/*
 * debug tracing
 */
#define dbgprintk(FMT, ...) \
	printk("[%-6.6s] "FMT"\n", current->comm, ##__VA_ARGS__)

#define kenter(FMT, ...) dbgprintk("==> %s("FMT")", __func__, ##__VA_ARGS__)
#define kleave(FMT, ...) dbgprintk("<== %s()"FMT"", __func__, ##__VA_ARGS__)
#define kdebug(FMT, ...) dbgprintk(FMT, ##__VA_ARGS__)

#ifdef __KDEBUG
#define _enter(FMT, ...) kenter(FMT, ##__VA_ARGS__)
#define _leave(FMT, ...) kleave(FMT, ##__VA_ARGS__)
#define _debug(FMT, ...) kdebug(FMT, ##__VA_ARGS__)

#elif defined(CONFIG_NETFS_DEBUG)
#define _enter(FMT, ...)			\
do {						\
	if (netfs_debug)			\
		kenter(FMT, ##__VA_ARGS__);	\
} while (0)

#define _leave(FMT, ...)			\
do {						\
	if (netfs_debug)			\
		kleave(FMT, ##__VA_ARGS__);	\
} while (0)

#define _debug(FMT, ...)			\
do {						\
	if (netfs_debug)			\
		kdebug(FMT, ##__VA_ARGS__);	\
} while (0)

#else
#define _enter(FMT, ...) no_printk("==> %s("FMT")", __func__, ##__VA_ARGS__)
#define _leave(FMT, ...) no_printk("<== %s()"FMT"", __func__, ##__VA_ARGS__)
#define _debug(FMT, ...) no_printk(FMT, ##__VA_ARGS__)
#endif
