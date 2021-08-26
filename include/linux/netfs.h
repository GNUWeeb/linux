/* SPDX-License-Identifier: GPL-2.0-or-later */
/* Network filesystem support services.
 *
 * Copyright (C) 2021 Red Hat, Inc. All Rights Reserved.
 * Written by David Howells (dhowells@redhat.com)
 *
 * See:
 *
 *	Documentation/filesystems/netfs_library.rst
 *
 * for a description of the network filesystem interface declared here.
 */

#ifndef _LINUX_NETFS_H
#define _LINUX_NETFS_H

#include <linux/workqueue.h>
#include <linux/fs.h>
#include <linux/pagemap.h>
#include <linux/uio.h>

struct scatterlist;
enum netfs_wreq_trace;

/*
 * Overload PG_private_2 to give us PG_fscache - this is used to indicate that
 * a page is currently backed by a local disk cache
 */
#define folio_test_fscache(folio)	folio_test_private_2(folio)
#define PageFsCache(page)		PagePrivate2((page))
#define SetPageFsCache(page)		SetPagePrivate2((page))
#define ClearPageFsCache(page)		ClearPagePrivate2((page))
#define TestSetPageFsCache(page)	TestSetPagePrivate2((page))
#define TestClearPageFsCache(page)	TestClearPagePrivate2((page))

/**
 * folio_start_fscache - Start an fscache write on a folio.
 * @folio: The folio.
 *
 * Call this function before writing a folio to a local cache.  Starting a
 * second write before the first one finishes is not allowed.
 */
static inline void folio_start_fscache(struct folio *folio)
{
	VM_BUG_ON_FOLIO(folio_test_private_2(folio), folio);
	folio_get(folio);
	folio_set_private_2(folio);
}

/**
 * folio_end_fscache - End an fscache write on a folio.
 * @folio: The folio.
 *
 * Call this function after the folio has been written to the local cache.
 * This will wake any sleepers waiting on this folio.
 */
static inline void folio_end_fscache(struct folio *folio)
{
	folio_end_private_2(folio);
}

/**
 * folio_wait_fscache - Wait for an fscache write on this folio to end.
 * @folio: The folio.
 *
 * If this folio is currently being written to a local cache, wait for
 * the write to finish.  Another write may start after this one finishes,
 * unless the caller holds the folio lock.
 */
static inline void folio_wait_fscache(struct folio *folio)
{
	folio_wait_private_2(folio);
}

/**
 * folio_wait_fscache_killable - Wait for an fscache write on this folio to end.
 * @folio: The folio.
 *
 * If this folio is currently being written to a local cache, wait
 * for the write to finish or for a fatal signal to be received.
 * Another write may start after this one finishes, unless the caller
 * holds the folio lock.
 *
 * Return:
 * - 0 if successful.
 * - -EINTR if a fatal signal was encountered.
 */
static inline int folio_wait_fscache_killable(struct folio *folio)
{
	return folio_wait_private_2_killable(folio);
}

static inline void set_page_fscache(struct page *page)
{
	folio_start_fscache(page_folio(page));
}

static inline void end_page_fscache(struct page *page)
{
	folio_end_private_2(page_folio(page));
}

static inline void wait_on_page_fscache(struct page *page)
{
	folio_wait_private_2(page_folio(page));
}

static inline int wait_on_page_fscache_killable(struct page *page)
{
	return folio_wait_private_2_killable(page_folio(page));
}

enum netfs_read_source {
	NETFS_FILL_WITH_ZEROES,
	NETFS_DOWNLOAD_FROM_SERVER,
	NETFS_READ_FROM_CACHE,
	NETFS_INVALID_READ,
} __mode(byte);

typedef void (*netfs_io_terminated_t)(void *priv, ssize_t transferred_or_error,
				      bool was_async);

/*
 * Per-inode description.  This must be directly after the inode struct.
 */
struct netfs_i_context {
	const struct netfs_request_ops *ops;
	struct list_head	pending_writes;	/* List of writes waiting to be begin */
	struct list_head	active_writes;	/* List of writes being applied */
	struct list_head	dirty_regions;	/* List of dirty regions in the pagecache */
	struct list_head	flush_groups;	/* FIFO of flushable groups */
#if IS_ENABLED(CONFIG_FSCACHE)
	struct fscache_cookie	*cache;
#endif
	loff_t			zero_point;	/* Size after which we assume there's no data
						 * on the server */
	unsigned long		flags;
#define NETFS_ICTX_NEW_CONTENT	0		/* Set if file has new content (create/trunc-0) */
#define NETFS_ICTX_GOT_CACHED_ZP 1		/* We read zero_point from the cache */
#define NETFS_ICTX_DO_RMW	2		/* Set if RMW required (no write streaming) */
#define NETFS_ICTX_ENCRYPTED	3		/* The file contents are encrypted */
	spinlock_t		lock;
	unsigned int		rsize;		/* Maximum read size */
	unsigned int		wsize;		/* Maximum write size */
	unsigned char		min_bshift;	/* log2 min block size for bounding box or 0 */
	unsigned char		obj_bshift;	/* log2 storage object shift (ceph/pnfs) or 0 */
	unsigned char		crypto_bshift;	/* log2 of crypto block size */
};

/*
 * Resources required to do operations on a cache.
 */
struct netfs_cache_resources {
	const struct netfs_cache_ops	*ops;
	void				*cache_priv;
	void				*cache_priv2;
	unsigned int			debug_id;	/* Cookie debug ID */
};

/*
 * Descriptor for a single component subrequest.
 */
struct netfs_read_subrequest {
	struct netfs_read_request *rreq;	/* Supervising read request */
	struct list_head	rreq_link;	/* Link in rreq->subrequests */
	struct iov_iter		iter;		/* Iterator for this subrequest */
	loff_t			start;		/* Where to start the I/O */
	size_t			len;		/* Size of the I/O */
	size_t			transferred;	/* Amount of data transferred */
	refcount_t		usage;
	short			error;		/* 0 or error that occurred */
	unsigned short		debug_index;	/* Index in list (for debugging output) */
	enum netfs_read_source	source;		/* Where to read from */
	unsigned long		flags;
#define NETFS_SREQ_WRITE_TO_CACHE	0	/* Set if should write to cache */
#define NETFS_SREQ_CLEAR_TAIL		1	/* Set if the rest of the read should be cleared */
#define NETFS_SREQ_SHORT_READ		2	/* Set if there was a short read from the cache */
#define NETFS_SREQ_SEEK_DATA_READ	3	/* Set if ->read() should SEEK_DATA first */
#define NETFS_SREQ_NO_PROGRESS		4	/* Set if we didn't manage to read any data */
};

enum netfs_read_origin {
	NETFS_READAHEAD,		/* This read was triggered by readahead */
	NETFS_SYNC_READ,		/* This read is a synchronous read */
	NETFS_READ_FOR_WRITE,		/* This read is to prepare a write */
} __mode(byte);

/*
 * Descriptor for a read helper request.  This is used to make multiple I/O
 * requests on a variety of sources and then stitch the result together.
 */
struct netfs_read_request {
	struct work_struct	work;
	struct inode		*inode;		/* The file being accessed */
	struct address_space	*mapping;	/* The mapping being accessed */
	struct netfs_dirty_region *for_write;	/* Write associated with or NULL */
	struct netfs_cache_resources cache_resources;
	struct list_head	subrequests;	/* Requests to fetch I/O from disk or net */
	struct xarray		buffer;		/* Decryption/decompression buffer */
	void			*netfs_priv;	/* Private data for the netfs */
	unsigned int		debug_id;
	atomic_t		nr_rd_ops;	/* Number of read ops in progress */
	size_t			submitted;	/* Amount submitted for I/O so far */
	size_t			len;		/* Length of the request */
	short			error;		/* 0 or error that occurred */
	enum netfs_read_origin	origin;		/* Origin of the read */
	loff_t			i_size;		/* Size of the file */
	loff_t			start;		/* Start position */
	pgoff_t			no_unlock_folio; /* Don't unlock this folio after read */
	refcount_t		usage;
	unsigned long		flags;
#define NETFS_RREQ_INCOMPLETE_IO	0	/* Some ioreqs terminated short or with error */
#define NETFS_RREQ_WRITE_TO_CACHE	1	/* Need to write to the cache */
#define NETFS_RREQ_NO_UNLOCK_FOLIO	2	/* Don't unlock no_unlock_folio on completion */
#define NETFS_RREQ_DONT_UNLOCK_FOLIOS	3	/* Don't unlock the folios on completion */
#define NETFS_RREQ_FAILED		4	/* The request failed */
#define NETFS_RREQ_IN_PROGRESS		5	/* Unlocked when the request completes */
#define NETFS_RREQ_DECRYPT		6	/* Decrypted when the request completes */
#define NETFS_RREQ_DENY_READAHEAD	7	/* Abort the readahead */
	const struct netfs_request_ops *netfs_ops;
};

/*
 * Descriptor for a set of writes that will need to be flushed together.
 *
 * These are maintained as a FIFO.  The frontmost group in the FIFO is the only
 * one that can be written from; the rearmost group in the FIFO is the only one
 * that can be modified.
 *
 * When a prospective write collides with a dirty region in an earlier group,
 * that group and all those in front of it have to be written out, in order,
 * before the modification can take place.
 */
struct netfs_flush_group {
	struct list_head	group_link;	/* Link in i_context->flush_groups */
	struct list_head	region_list;	/* List of regions in this group */
	loff_t			i_size;		/* Size of the file for this group */
	void			*netfs_priv;
	refcount_t		ref;
	unsigned long		flags;
#define NETFS_FGROUP_FLUSHED		0	/* Group has been flushed */
#define NETFS_FGROUP_PARENT_FLUSHED	1	/* Parent group has been flushed from this one */
};

struct netfs_range {
	unsigned long long	start;		/* Start of region */
	unsigned long long	end;		/* End of region */
};

/* State of a netfs_dirty_region */
enum netfs_region_state {
	NETFS_REGION_IS_PENDING,	/* Proposed write is waiting on an active write */
	NETFS_REGION_IS_RESERVED,	/* Writable region is reserved, waiting on flushes */
	NETFS_REGION_IS_ACTIVE,		/* Write is actively modifying the pagecache */
	NETFS_REGION_IS_DIRTY,		/* Region is dirty */
	NETFS_REGION_IS_FLUSHING,	/* Region is being flushed */
	NETFS_REGION_IS_COMPLETE,	/* Region has been completed (stored/invalidated) */
} __attribute__((mode(byte)));

enum netfs_region_type {
	NETFS_REGION_ORDINARY,		/* Ordinary write */
	NETFS_REGION_DIO,		/* Direct I/O write */
	NETFS_REGION_DSYNC,		/* O_DSYNC/RWF_DSYNC write */
	NETFS_REGION_CACHE_COPY,	/* Data to be written to cache only */
} __attribute__((mode(byte)));

/*
 * Descriptor for a dirty region that has a common set of parameters and can
 * feasibly be written back in one go.  These are held in an ordered list.
 *
 * Regions are not allowed to overlap, though they may be merged.
 */
struct netfs_dirty_region {
	struct netfs_flush_group *group;
	struct list_head	proc_link;	/* Link in /proc/fs/netfs/regions */
	struct list_head	active_link;	/* Link in i_context->pending/active_writes */
	struct list_head	dirty_link;	/* Link in i_context->dirty_regions */
	struct list_head	flush_link;	/* Link in group->region_list or
						 * i_context->flush_queue */
	spinlock_t		lock;
	void			*netfs_priv;	/* Private data for the netfs */
	struct netfs_range	bounds;		/* Bounding box including all affected pages */
	struct netfs_range	reserved;	/* The region reserved against other writes */
	struct netfs_range	dirty;		/* The region that has been modified */
	size_t			credit;		/* Amount of credit used */
	enum netfs_region_type	type;
	enum netfs_region_state	state;
	unsigned long		flags;
#define NETFS_REGION_SYNC	0		/* Set if metadata sync required (RWF_SYNC) */
#define NETFS_REGION_FLUSH_Q	1		/* Set if region is on flush queue */
#define NETFS_REGION_SUPERSEDED	2		/* Set if region is being superseded */
	unsigned int		debug_id;
	refcount_t		ref;
};

enum netfs_write_dest {
	NETFS_UPLOAD_TO_SERVER,
	NETFS_WRITE_TO_CACHE,
	NETFS_INVALID_WRITE,
} __mode(byte);

/*
 * Descriptor for a write operation.  Each operation represents an individual
 * write to a server, a cache, a journal, etc..
 *
 * The source buffer iterator is persistent for the life of the
 * netfs_write_operation struct and the pages it points to can be relied on to
 * exist for the duration.
 */
struct netfs_write_operation {
	struct netfs_write_request *wreq;	/* Supervising write request */
	struct work_struct	work;
	struct list_head	wreq_link;	/* Link in wreq->operations */
	struct iov_iter		source;		/* Persistent buffer to obtain data from */
	loff_t			start;		/* Where to start the I/O */
	size_t			len;		/* Size of the I/O */
	size_t			transferred;	/* Amount of data transferred */
	refcount_t		ref;
	short			error;		/* 0 or error that occurred */
	unsigned short		debug_index;	/* Index in list (for debugging output) */
	enum netfs_write_dest	dest;		/* Where to write to */
};

/*
 * Descriptor for a write request.  This is used to manage the preparation and
 * storage of a sequence of dirty data - its compression/encryption and its
 * writing to one or more servers and the cache.
 *
 * The prepared data is buffered here, and write operations are used to
 * distribute the buffer to various destinations (servers, caches, etc.).
 */
struct netfs_write_request {
	struct work_struct	work;
	struct inode		*inode;		/* The file being accessed */
	struct address_space	*mapping;	/* The mapping being accessed */
	struct netfs_cache_resources cache_resources;
	struct xarray		buffer;		/* Buffer for encrypted/compressed data */
	struct list_head	proc_link;	/* Link in netfs_wreqs */
	struct list_head	regions;	/* The contributory regions (by ->flush_link)  */
	struct list_head	operations;	/* The write operations involved */
	struct netfs_flush_group *group;	/* Flush group this write is from */
	rwlock_t		regions_lock;	/* Lock for ->regions */
	void			*netfs_priv;	/* Private data for the netfs */
	unsigned int		debug_id;
	unsigned char		n_ops;		/* Number of ops allocated */
	short			error;		/* 0 or error that occurred */
	struct netfs_range	coverage;	/* Range covered by the request */
	pgoff_t			first;		/* First page included */
	pgoff_t			last;		/* Last page included */
	atomic_t		outstanding;	/* Number of outstanding writes */
	refcount_t		usage;
	unsigned long		flags;
#define NETFS_WREQ_WRITE_TO_CACHE	0	/* Need to write to the cache */
#define NETFS_WREQ_BUFFERED		1	/* Data is held in ->buffer */
	const struct netfs_request_ops *netfs_ops;
};

enum netfs_write_compatibility {
	NETFS_WRITES_COMPATIBLE,	/* Dirty regions can be directly merged */
	NETFS_WRITES_SUPERSEDE,		/* Second write can supersede the first without first
					 * having to be flushed (eg. authentication, DSYNC) */
	NETFS_WRITES_INCOMPATIBLE,	/* Second write must wait for first (eg. DIO, ceph snap) */
};

/*
 * Operations the network filesystem can/must provide to the helpers.
 */
struct netfs_request_ops {
	/* Read request handling */
	void (*init_rreq)(struct netfs_read_request *rreq, struct file *file);
	int (*begin_cache_operation)(struct netfs_read_request *rreq);
	void (*expand_readahead)(struct netfs_read_request *rreq);
	bool (*clamp_length)(struct netfs_read_subrequest *subreq);
	void (*issue_op)(struct netfs_read_subrequest *subreq);
	bool (*is_still_valid)(struct netfs_read_request *rreq);
	int (*check_write_begin)(struct file *file, loff_t pos, unsigned len,
				 struct folio *folio, void **_fsdata);
	void (*done)(struct netfs_read_request *rreq);
	void (*cleanup)(struct address_space *mapping, void *netfs_priv);

	/* Flush group handling */
	void (*free_flush_group)(struct netfs_i_context *ctx,
				 struct netfs_flush_group *group);

	/* Dirty region handling */
	void (*init_dirty_region)(struct netfs_dirty_region *region, struct file *file);
	void (*split_dirty_region)(struct netfs_dirty_region *region);
	void (*free_dirty_region)(struct netfs_dirty_region *region);
	enum netfs_write_compatibility (*is_write_compatible)(
		struct netfs_i_context *ctx,
		struct netfs_dirty_region *old_region,
		struct netfs_dirty_region *candidate);
	bool (*check_compatible_write)(struct netfs_dirty_region *region, struct file *file);
	void (*update_i_size)(struct file *file, loff_t i_size);

	/* Write request handling */
	void (*init_wreq)(struct netfs_write_request *wreq);
	void (*create_write_operations)(struct netfs_write_request *wreq);
	void (*free_write_operation)(struct netfs_write_operation *op);
	void (*invalidate_cache)(struct netfs_write_request *wreq);

	/* Content encryption */
	bool (*encrypt_block)(struct netfs_write_request *wreq, loff_t pos, size_t len,
			      struct scatterlist *source_sg, unsigned int n_source,
			      struct scatterlist *dest_sg, unsigned int n_dest);
	int (*decrypt_block)(struct netfs_read_request *rreq, loff_t pos, size_t len,
			     struct scatterlist *source_sg, unsigned int n_source,
			     struct scatterlist *dest_sg, unsigned int n_dest);
};

/*
 * Table of operations for access to a cache.  This is obtained by
 * rreq->ops->begin_cache_operation().
 */
struct netfs_cache_ops {
	/* End an operation */
	void (*end_operation)(struct netfs_cache_resources *cres);

	/* Read data from the cache */
	int (*read)(struct netfs_cache_resources *cres,
		    loff_t start_pos,
		    struct iov_iter *iter,
		    bool seek_data,
		    netfs_io_terminated_t term_func,
		    void *term_func_priv);

	/* Write data to the cache */
	int (*write)(struct netfs_cache_resources *cres,
		     loff_t start_pos,
		     struct iov_iter *iter,
		     netfs_io_terminated_t term_func,
		     void *term_func_priv);

	/* Expand readahead request */
	void (*expand_readahead)(struct netfs_cache_resources *cres,
				 loff_t *_start, size_t *_len, loff_t i_size);

	/* Prepare a read operation, shortening it to a cached/uncached
	 * boundary as appropriate.
	 */
	enum netfs_read_source (*prepare_read)(struct netfs_read_subrequest *subreq,
					       loff_t i_size);

	/* Prepare a write operation, working out what part of the write we can
	 * actually do.
	 */
	int (*prepare_write)(struct netfs_cache_resources *cres,
			     loff_t *_start, size_t *_len, loff_t i_size);
};

struct readahead_control;
extern void netfs_readahead(struct readahead_control *);
extern int netfs_readpage(struct file *, struct page *);
extern int netfs_write_begin(struct file *, struct address_space *,
			     loff_t, unsigned int, unsigned int, struct folio **,
			     void **);
extern ssize_t netfs_file_write_iter(struct kiocb *iocb, struct iov_iter *from);
extern int netfs_writepages(struct address_space *mapping, struct writeback_control *wbc);
extern void netfs_invalidatepage(struct page *page, unsigned int offset, unsigned int length);
extern int netfs_releasepage(struct page *page, gfp_t gfp_flags);

extern void netfs_subreq_terminated(struct netfs_read_subrequest *, ssize_t, bool);
extern void netfs_stats_show(struct seq_file *);
extern struct netfs_flush_group *netfs_new_flush_group(struct inode *, void *);
extern struct netfs_write_operation *netfs_create_write_operation(
	struct netfs_write_request *wreq, enum netfs_write_dest dest,
	loff_t start, size_t len, work_func_t worker);
extern void netfs_put_write_request(struct netfs_write_request *wreq,
				    bool was_async, enum netfs_wreq_trace what);
extern void netfs_queue_write_operation(struct netfs_write_operation *op);
extern void netfs_get_write_operation(struct netfs_write_operation *op,
				      enum netfs_wreq_trace what);
extern void netfs_put_write_operation(struct netfs_write_operation *op,
				      bool was_async, enum netfs_wreq_trace what);
extern void netfs_write_operation_completed(void *_op, ssize_t transferred_or_error,
					    bool was_async);

/**
 * netfs_i_context - Get the netfs inode context from the inode
 * @inode: The inode to query
 *
 * This function gets the netfs lib inode context from the network filesystem's
 * inode.  It expects it to follow on directly from the VFS inode struct.
 */
static inline struct netfs_i_context *netfs_i_context(struct inode *inode)
{
	return (struct netfs_i_context *)(inode + 1);
}

static inline void netfs_i_context_init(struct inode *inode,
					const struct netfs_request_ops *ops)
{
	struct netfs_i_context *ctx = netfs_i_context(inode);

	ctx->ops = ops;
	ctx->zero_point = i_size_read(inode);
	ctx->min_bshift = 0;
	ctx->obj_bshift = 0;
	INIT_LIST_HEAD(&ctx->pending_writes);
	INIT_LIST_HEAD(&ctx->active_writes);
	INIT_LIST_HEAD(&ctx->dirty_regions);
	INIT_LIST_HEAD(&ctx->flush_groups);
	spin_lock_init(&ctx->lock);
}

/**
 * netfs_resize_file - Note that a file got resized
 * @inode: The inode being resized
 * @new_i_size: The new file size
 *
 * Inform the netfs lib that a file got resized so that it can adjust its state.
 */
static inline void netfs_resize_file(struct inode *inode, loff_t new_i_size)
{
	struct netfs_i_context *ctx = netfs_i_context(inode);

	if (new_i_size < ctx->zero_point)
		ctx->zero_point = new_i_size;
}

/**
 * netfs_i_cookie - Get the cache cookie from the inode
 * @inode: The inode to query
 *
 * Get the caching cookie (if enabled) from the network filesystem's inode.
 */
static inline struct fscache_cookie *netfs_i_cookie(struct inode *inode)
{
#ifdef CONFIG_FSCACHE
	struct netfs_i_context *ctx = netfs_i_context(inode);
	return ctx->cache;
#else
	return NULL;
#endif
 }

#endif /* _LINUX_NETFS_H */
