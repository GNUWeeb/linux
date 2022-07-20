/* SPDX-License-Identifier: GPL-2.0 */
#ifndef _ASM_X86_LINKAGE_H
#define _ASM_X86_LINKAGE_H

#include <linux/stringify.h>
#include <asm/ibt.h>

#undef notrace
#define notrace __attribute__((no_instrument_function))

#ifdef CONFIG_X86_32
#define asmlinkage CPP_ASMLINKAGE __attribute__((regparm(0)))
#endif /* CONFIG_X86_32 */

#ifdef __ASSEMBLY__

#if CONFIG_FUNCTION_ALIGNMENT == 16
# define __ALIGN		.p2align 4, 0x90
# define __ALIGN_STR		__stringify(__ALIGN)
# define FUNCTION_ALIGNMENT	16
#elif CONFIG_FUNCTION_ALIGNMENT == 32
# define __ALIGN		.p2align 5, 0x90
# define __ALIGN_STR		__stringify(__ALIGN)
# define FUNCTION_ALIGNMENT	32
#endif

#if defined(CONFIG_RETHUNK) && !defined(__DISABLE_EXPORTS) && !defined(BUILD_VDSO)
#define RET	jmp __x86_return_thunk
#else /* CONFIG_RETPOLINE */
#ifdef CONFIG_SLS
#define RET	ret; int3
#else
#define RET	ret
#endif
#endif /* CONFIG_RETPOLINE */

#else /* __ASSEMBLY__ */

#if defined(CONFIG_RETHUNK) && !defined(__DISABLE_EXPORTS) && !defined(BUILD_VDSO)
#define ASM_RET	"jmp __x86_return_thunk\n\t"
#else /* CONFIG_RETPOLINE */
#ifdef CONFIG_SLS
#define ASM_RET	"ret; int3\n\t"
#else
#define ASM_RET	"ret\n\t"
#endif
#endif /* CONFIG_RETPOLINE */

#endif /* __ASSEMBLY__ */

#ifndef _NO_CALLTHUNKS
#if defined(CONFIG_CALL_THUNKS_IN_PADDING)
# if CONFIG_FUNCTION_ALIGNMENT == 16
#  define __FUNC_ALIGN		.p2align 4, 0x90; .skip 16, 0xCC;
#  define ASM_FUNC_ALIGN	".p2align 4, 0x90; .skip 16, 0xCC;"
#  define SYM_F_ALIGN		__FUNC_ALIGN
# elif CONFIG_FUNCTION_ALIGNMENT == 32
#  define __FUNC_ALIGN		.p2align 5, 0x90; .skip 32, 0xCC;
#  define ASM_FUNC_ALIGN	".p2align 5, 0x90; .skip 32, 0xCC;"
#  define SYM_F_ALIGN		__FUNC_ALIGN
# endif
#else /* CONFIG_CALL_THUNKS_IN_PADDING */
# if CONFIG_FUNCTION_ALIGNMENT == 16
#  define __FUNC_ALIGN		.p2align 4, 0x90;
#  define ASM_FUNC_ALIGN	".p2align 4, 0x90;"
#  define SYM_F_ALIGN		__FUNC_ALIGN
# elif CONFIG_FUNCTION_ALIGNMENT == 32
#  define __FUNC_ALIGN		.p2align 5, 0x90;
#  define ASM_FUNC_ALIGN	".p2align 5, 0x90;"
#  define SYM_F_ALIGN		__FUNC_ALIGN
# endif
#endif /* !CONFIG_CALL_THUNKS_IN_PADDING */
#endif /* !_D_NO_CALLTHUNKS */

#ifndef __FUNC_ALIGN
# define __FUNC_ALIGN
# define ASM_FUNC_ALIGN		""
# define SYM_F_ALIGN		SYM_A_ALIGN
#endif

/* SYM_FUNC_START -- use for global functions */
#define SYM_FUNC_START(name)				\
	SYM_START(name, SYM_L_GLOBAL, SYM_F_ALIGN)	\
	ENDBR

/* SYM_FUNC_START_NOALIGN -- use for global functions, w/o alignment */
#define SYM_FUNC_START_NOALIGN(name)			\
	SYM_START(name, SYM_L_GLOBAL, SYM_A_NONE)	\
	ENDBR

/* SYM_FUNC_START_LOCAL -- use for local functions */
#define SYM_FUNC_START_LOCAL(name)			\
	SYM_START(name, SYM_L_LOCAL, SYM_F_ALIGN)	\
	ENDBR

/* SYM_FUNC_START_LOCAL_NOALIGN -- use for local functions, w/o alignment */
#define SYM_FUNC_START_LOCAL_NOALIGN(name)		\
	SYM_START(name, SYM_L_LOCAL, SYM_A_NONE)	\
	ENDBR

/* SYM_FUNC_START_WEAK -- use for weak functions */
#define SYM_FUNC_START_WEAK(name)			\
	SYM_START(name, SYM_L_WEAK, SYM_F_ALIGN)	\
	ENDBR

/* SYM_FUNC_START_WEAK_NOALIGN -- use for weak functions, w/o alignment */
#define SYM_FUNC_START_WEAK_NOALIGN(name)		\
	SYM_START(name, SYM_L_WEAK, SYM_A_NONE)		\
	ENDBR

#endif /* _ASM_X86_LINKAGE_H */

