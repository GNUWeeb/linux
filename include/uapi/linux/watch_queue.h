/* SPDX-License-Identifier: GPL-2.0 WITH Linux-syscall-note */
#ifndef _UAPI_LINUX_WATCH_QUEUE_H
#define _UAPI_LINUX_WATCH_QUEUE_H

#include <linux/types.h>

enum watch_notification_type {
	WATCH_TYPE_META		= 0,	/* Special record */
	WATCH_TYPE___NR		= 1
};

enum watch_meta_notification_subtype {
	WATCH_META_SKIP_NOTIFICATION	= 0,	/* Just skip this record */
	WATCH_META_REMOVAL_NOTIFICATION	= 1,	/* Watched object was removed */
};

#define WATCH_LENGTH_GRANULARITY sizeof(__u64)

/*
 * Notification record header.  This is aligned to 64-bits so that subclasses
 * can contain __u64 fields.
 */
struct watch_notification {
	__u32			type:24;	/* enum watch_notification_type */
	__u32			subtype:8;	/* Type-specific subtype (filterable) */
	__u32			info;
#define WATCH_INFO_LENGTH	0x0000003f	/* Length of record / sizeof(watch_notification) */
#define WATCH_INFO_LENGTH__SHIFT 0
#define WATCH_INFO_ID		0x0000ff00	/* ID of watchpoint, if type-appropriate */
#define WATCH_INFO_ID__SHIFT	8
#define WATCH_INFO_TYPE_INFO	0xffff0000	/* Type-specific info */
#define WATCH_INFO_TYPE_INFO__SHIFT 16
#define WATCH_INFO_FLAG_0	0x00010000	/* Type-specific info, flag bit 0 */
#define WATCH_INFO_FLAG_1	0x00020000	/* ... */
#define WATCH_INFO_FLAG_2	0x00040000
#define WATCH_INFO_FLAG_3	0x00080000
#define WATCH_INFO_FLAG_4	0x00100000
#define WATCH_INFO_FLAG_5	0x00200000
#define WATCH_INFO_FLAG_6	0x00400000
#define WATCH_INFO_FLAG_7	0x00800000
} __attribute__((aligned(WATCH_LENGTH_GRANULARITY)));

struct watch_queue_buffer {
	union {
		/* The first few entries are special, containing the
		 * ring management variables.
		 */
		struct {
			struct watch_notification watch; /* WATCH_TYPE_META */
			__u32		head;		/* Ring head index */
			__u32		tail;		/* Ring tail index */
			__u32		mask;		/* Ring index mask */
			__u32		__reserved;
		} meta;
		struct watch_notification slots[0];
	};
};

/*
 * The Metadata pseudo-notification message uses a flag bits in the information
 * field to convey the fact that messages have been lost.  We can only use a
 * single bit in this manner per word as some arches that support SMP
 * (eg. parisc) have no kernel<->user atomic bit ops.
 */
#define WATCH_INFO_NOTIFICATIONS_LOST WATCH_INFO_FLAG_0

#endif /* _UAPI_LINUX_WATCH_QUEUE_H */
