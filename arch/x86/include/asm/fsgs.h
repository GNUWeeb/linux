#ifndef _ASM_FSGS_H
#define _ASM_FSGS_H 1

#ifndef __ASSEMBLY__

#ifdef CONFIG_X86_64

#include <asm/msr-index.h>

/* Read FSBASE for the current task. */
static inline unsigned long read_fs_base(void)
{
	unsigned long base;

	rdmsrl(MSR_FS_BASE, base);
	return base;
}

/* Read GSBASE for the current task. */
static inline unsigned long read_inactive_gs_base(void)
{
	unsigned long base;

	rdmsrl(MSR_KERNEL_GS_BASE, base);
	return base;
}

#endif /* CONFIG_X86_64 */

#endif /* __ASSEMBLY__ */

#endif
