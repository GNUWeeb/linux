/* Use ISO C++11 intrinsics to implement 32-bit atomic ops.
 *
 * Copyright (C) 2016 Red Hat, Inc. All Rights Reserved.
 * Written by David Howells (dhowells@redhat.com)
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public Licence
 * as published by the Free Software Foundation; either version
 * 2 of the Licence, or (at your option) any later version.
 */

#ifndef _ASM_GENERIC_ISO_ATOMIC_H
#define _ASM_GENERIC_ISO_ATOMIC_H

#include <linux/compiler.h>
#include <linux/types.h>

#define ATOMIC_INIT(i)	{ (i) }

#define atomic_val int
#define atomic_prefix(x) atomic##x
#define __atomic_prefix(x) __atomic##x
#include <asm-generic/iso-atomic-template.h>
#undef atomic_val
#undef atomic_prefix
#undef __atomic_prefix

#endif /* _ASM_GENERIC_ISO_ATOMIC_H */
