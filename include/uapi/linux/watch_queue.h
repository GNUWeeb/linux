/* SPDX-License-Identifier: GPL-2.0 WITH Linux-syscall-note */
#ifndef _UAPI_LINUX_WATCH_QUEUE_H
#define _UAPI_LINUX_WATCH_QUEUE_H

#include <linux/types.h>
#include <linux/ioctl.h>

#define IOC_WATCH_QUEUE_SET_SIZE	_IO('s', 0x01)	/* Set the size in pages */
#define IOC_WATCH_QUEUE_SET_FILTER	_IO('s', 0x02)	/* Set the filter */

enum watch_notification_type {
	WATCH_TYPE_META		= 0,	/* Special record */
	WATCH_TYPE_MOUNT_NOTIFY	= 1,	/* Mount notification record */
	WATCH_TYPE_SB_NOTIFY	= 2,	/* Superblock notification */
	WATCH_TYPE_KEY_NOTIFY	= 3,	/* Key/keyring change notification */
#define WATCH_TYPE___NR 4
};

enum watch_meta_notification_subtype {
	WATCH_META_SKIP_NOTIFICATION	= 0,	/* Just skip this record */
	WATCH_META_REMOVAL_NOTIFICATION	= 1,	/* Watched object was removed */
};

/*
 * Notification record
 */
struct watch_notification {
	__u32			type:24;	/* enum watch_notification_type */
	__u32			subtype:8;	/* Type-specific subtype (filterable) */
	__u32			info;
#define WATCH_INFO_OVERRUN	0x00000001	/* Event(s) lost due to overrun */
#define WATCH_INFO_ENOMEM	0x00000002	/* Event(s) lost due to ENOMEM */
#define WATCH_INFO_RECURSIVE	0x00000004	/* Change was recursive */
#define WATCH_INFO_LENGTH	0x000001f8	/* Length of record / sizeof(watch_notification) */
#define WATCH_INFO_IN_SUBTREE	0x00000200	/* Change was not at watched root */
#define WATCH_INFO_TYPE_FLAGS	0x00ff0000	/* Type-specific flags */
#define WATCH_INFO_FLAG_0	0x00010000
#define WATCH_INFO_FLAG_1	0x00020000
#define WATCH_INFO_FLAG_2	0x00040000
#define WATCH_INFO_FLAG_3	0x00080000
#define WATCH_INFO_FLAG_4	0x00100000
#define WATCH_INFO_FLAG_5	0x00200000
#define WATCH_INFO_FLAG_6	0x00400000
#define WATCH_INFO_FLAG_7	0x00800000
#define WATCH_INFO_ID		0xff000000	/* ID of watchpoint */
};

#define WATCH_LENGTH_SHIFT	3

struct watch_queue_buffer {
	union {
		/* The first few entries are special, containing the
		 * ring management variables.
		 */
		struct {
			struct watch_notification watch; /* WATCH_TYPE_SKIP */
			volatile __u32	head;		/* Ring head index */
			volatile __u32	tail;		/* Ring tail index */
			__u32		mask;		/* Ring index mask */
		} meta;
		struct watch_notification slots[0];
	};
};

/*
 * Notification filtering rules (IOC_WATCH_QUEUE_SET_FILTER).
 */
struct watch_notification_type_filter {
	__u32	type;			/* Type to apply filter to */
	__u32	info_filter;		/* Filter on watch_notification::info */
	__u32	info_mask;		/* Mask of relevant bits in info_filter */
	__u32	subtype_filter[8];	/* Bitmask of subtypes to filter on */
};

struct watch_notification_filter {
	__u32	nr_filters;		/* Number of filters */
	__u32	__reserved;		/* Must be 0 */
	struct watch_notification_type_filter filters[];
};

/*
 * Type of key/keyring change notification.
 */
enum key_notification_subtype {
	NOTIFY_KEY_INSTANTIATED	= 0, /* Key was instantiated (aux is error code) */
	NOTIFY_KEY_UPDATED	= 1, /* Key was updated */
	NOTIFY_KEY_LINKED	= 2, /* Key (aux) was added to watched keyring */
	NOTIFY_KEY_UNLINKED	= 3, /* Key (aux) was removed from watched keyring */
	NOTIFY_KEY_CLEARED	= 4, /* Keyring was cleared */
	NOTIFY_KEY_REVOKED	= 5, /* Key was revoked */
	NOTIFY_KEY_INVALIDATED	= 6, /* Key was invalidated */
	NOTIFY_KEY_SETATTR	= 7, /* Key's attributes got changed */
};

/*
 * Key/keyring notification record.
 * - watch.type = WATCH_TYPE_KEY_NOTIFY
 * - watch.subtype = enum key_notification_type
 */
struct key_notification {
	struct watch_notification watch;
	__u32	key_id;		/* The key/keyring affected */
	__u32	aux;		/* Per-type auxiliary data */
};

/*
 * Type of mount topology change notification.
 */
enum mount_notification_subtype {
	NOTIFY_MOUNT_NEW_MOUNT	= 0, /* New mount added */
	NOTIFY_MOUNT_UNMOUNT	= 1, /* Mount removed manually */
	NOTIFY_MOUNT_EXPIRY	= 2, /* Automount expired */
	NOTIFY_MOUNT_READONLY	= 3, /* Mount R/O state changed */
	NOTIFY_MOUNT_SETATTR	= 4, /* Mount attributes changed */
	NOTIFY_MOUNT_MOVE_FROM	= 5, /* Mount moved from here */
	NOTIFY_MOUNT_MOVE_TO	= 6, /* Mount moved to here (compare op_id) */
};

/*
 * Mount topology/configuration change notification record.
 * - watch.type = WATCH_TYPE_MOUNT_NOTIFY
 * - watch.subtype = enum mount_notification_subtype
 */
struct mount_notification {
	struct watch_notification watch; /* WATCH_TYPE_MOUNT_NOTIFY */
	__u32	triggered_on;		/* The mount that the notify was on */
	__u32	changed_mount;		/* The mount that got changed */
};

/*
 * Type of superblock notification.
 */
enum superblock_notification_type {
	NOTIFY_SUPERBLOCK_READONLY	= 0, /* Filesystem toggled between R/O and R/W */
	NOTIFY_SUPERBLOCK_ERROR		= 1, /* Error in filesystem or blockdev */
	NOTIFY_SUPERBLOCK_EDQUOT	= 2, /* EDQUOT notification */
	NOTIFY_SUPERBLOCK_NETWORK	= 3, /* Network status change */
};

/*
 * Superblock notification record.
 * - watch.type = WATCH_TYPE_MOUNT_NOTIFY
 * - watch.subtype = enum superblock_notification_subtype
 */
struct superblock_notification {
	struct watch_notification watch; /* WATCH_TYPE_SB_NOTIFY */
	__u64	sb_id;			/* 64-bit superblock ID [fsinfo_ids::f_sb_id] */
};

struct superblock_error_notification {
	struct superblock_notification s; /* subtype = notify_superblock_error */
	__u32	error_number;
	__u32	error_cookie;
};

#endif /* _UAPI_LINUX_WATCH_QUEUE_H */
