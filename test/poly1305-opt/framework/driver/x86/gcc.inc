#ifndef BASE_GCC_X86_S
#define BASE_GCC_X86_S

#include "asmopt_internal.h"

#if !defined(HAVE_SLASHMACRO) && !defined(HAVE_DOLLARMACRO)
	#error Unknown gnu as macro parameter convention! Run ./configure
#endif

#define IS_X86_32 (defined(__i386__))
#define IS_X86_64 (defined(__x86_64__))
#define IS_ELF (defined(__ELF__))
#define IS_MACH (defined(__MACH__))
#define IS_WIN32 (IS_X86_32 && (defined(_WIN32) || defined(__CYGWIN__)))
#define IS_WIN64 (IS_X86_64 && (defined(_WIN64) || defined(__CYGWIN__)))

#if (IS_WIN64)
	/* handles 0-6 arguments and optional saving of the upper 8 xmm registers */
	.macro WIN64STUBFN name, args, xmmused
		\name:; _\name:;

		subq $(184), %rsp
		movdqa %xmm6, 0(%rsp)
		movdqa %xmm7, 16(%rsp)
		.if \xmmused > 8
			movdqa %xmm8, 32(%rsp)
			movdqa %xmm9, 48(%rsp)
			movdqa %xmm10, 64(%rsp)
			movdqa %xmm11, 80(%rsp)
			movdqa %xmm12, 96(%rsp)
			movdqa %xmm13, 112(%rsp)
			movdqa %xmm14, 128(%rsp)
			movdqa %xmm15, 144(%rsp)
		.endif
		movq %rdi, 160(%rsp)
		movq %rsi, 168(%rsp)
		movq %rcx, %rdi
		movq %rdx, %rsi
		movq %r8, %rdx
		movq %r9, %rcx
		.if \args >= 5
			movq 224(%rsp), %r8
		.endif
		.if \args >= 6
			movq 232(%rsp), %r9
		.endif
		call thunk_\name
		movdqa 0(%rsp), %xmm6
		movdqa 16(%rsp), %xmm7
		.if \xmmused > 8
			movdqa 32(%rsp), %xmm8
			movdqa 48(%rsp), %xmm9
			movdqa 64(%rsp), %xmm10
			movdqa 80(%rsp), %xmm11
			movdqa 96(%rsp), %xmm12
			movdqa 112(%rsp), %xmm13
			movdqa 128(%rsp), %xmm14
			movdqa 144(%rsp), %xmm15
		.endif
		movq 160(%rsp), %rdi
		movq 168(%rsp), %rsi
		addq $(184), %rsp
		ret
	thunk_\name:
	.endm

	.macro FN name
		WIN64STUBFN \name, 4, 16
	.endm

	.macro FN_EXT name, args, xmmused
		WIN64STUBFN \name, \args, \xmmused
	.endm

	.macro FN_END name
	.endm

	.macro HIDDEN name
	.endm
#elif (IS_WIN32)
	.macro FN name
		\name:
		_\name:
	.endm

	.macro FN_EXT name, args, xmmused
		FN \name
	.endm

	.macro FN_END name
	.endm

	.macro HIDDEN name
	.endm
#elif (IS_ELF)
	.macro FN name
		\name:
		_\name:
	.endm

	.macro FN_EXT name, args, xmmused
		FN \name
	.endm

	.macro FN_END name
		.size \name, .-\name
		.size _\name, .-_\name
		.type \name, @function
	 	.type _\name, @function
	.endm

	.macro HIDDEN name
	#if defined(HAVE_AS_HIDDEN)
		.hidden \name
		.hidden _\name
	#endif
	.endm

	/* set NX for stack */
	.section .note.GNU-stack,"",@progbits
#elif (IS_MACH)
	.macro FN name
	#if defined(HAVE_SLASHMACRO)
		\name:
		_\name:
	#elif defined(HAVE_DOLLARMACRO)
		$0:
		_$0:
	#endif
	.endm

	.macro FN_EXT name, args, xmmused
	#if defined(HAVE_SLASHMACRO)
		FN \name
	#elif defined(HAVE_DOLLARMACRO)
		FN $0
	#endif
	.endm

	.macro FN_END name
	.endm

	.macro HIDDEN name
	#if defined(HAVE_AS_PRIVATE_EXTERN)
	#if defined(HAVE_SLASHMACRO)
		.private_extern \name
		.private_extern _\name
	#elif defined(HAVE_DOLLARMACRO)
		.private_extern $0
		.private_extern _$0
	#endif
	#endif
	.endm
#endif

/* put everything in the code segment to simplify things */
#if (IS_MACH)
	.macro SECTION_TEXT
		.section __TEXT,__text,regular
	.endm

	.macro SECTION_RODATA
		.section __TEXT,__text,regular
	.endm
#else
	/* put everything in the code segment to simplify things */
	.macro SECTION_TEXT
		.text
	.endm

	.macro SECTION_RODATA
		.text
	.endm
#endif

/* declare a global function */
.macro GLOBAL name
#if defined(HAVE_SLASHMACRO)
	.globl \name
	.globl _\name
#elif defined(HAVE_DOLLARMACRO)
	.globl $0
	.globl _$0
#endif
.endm

.macro FN_LOCAL_PREFIX name
#if defined(HAVE_SLASHMACRO)
	FN LOCAL_PREFIX(\name)
#elif defined(HAVE_DOLLARMACRO)
	FN LOCAL_PREFIX($0)
#endif
.endm

.macro FN_EXT_LOCAL_PREFIX name, args, xmmused
#if defined(HAVE_SLASHMACRO)
	FN_EXT LOCAL_PREFIX(\name), \args, \xmmused
#elif defined(HAVE_DOLLARMACRO)
	FN_EXT LOCAL_PREFIX($0), $1, $2
#endif
.endm

.macro FN_END_LOCAL_PREFIX name
#if defined(HAVE_SLASHMACRO)
	FN_END LOCAL_PREFIX(\name)
#elif defined(HAVE_DOLLARMACRO)
	FN_END LOCAL_PREFIX($0)
#endif
.endm

.macro GLOBAL_LOCAL_PREFIX name
#if defined(HAVE_SLASHMACRO)
	GLOBAL LOCAL_PREFIX(\name)
	HIDDEN LOCAL_PREFIX(\name)
#elif defined(HAVE_DOLLARMACRO)
	GLOBAL LOCAL_PREFIX($0)
	HIDDEN LOCAL_PREFIX($0)
#endif
.endm

.macro GLOBAL_HIDDEN_FN name
#if defined(HAVE_SLASHMACRO)
	GLOBAL \name
	HIDDEN \name
	FN \name
#elif defined(HAVE_DOLLARMACRO)
	GLOBAL $0
	HIDDEN $0
	FN $0
#endif
.endm

.macro GLOBAL_HIDDEN_FN_EXT name, args, xmmused
#if defined(HAVE_SLASHMACRO)
	GLOBAL \name
	HIDDEN \name
	FN_EXT \name, \args, \xmmused
#elif defined(HAVE_DOLLARMACRO)
	GLOBAL $0
	HIDDEN $0
	FN_EXT $0, $1, $2
#endif
.endm

/* pic support */
.macro LOAD_VAR_PIC var, reg
#if (IS_X86_32)
	#if defined(HAVE_SLASHMACRO)
		call 1f
		1:
		popl \reg
		leal \var - 1b(\reg), \reg
	#elif defined(HAVE_DOLLARMACRO)
		call 1f
		1:
		popl $1
		leal $0 - 1b($1), $1
	#endif
#else
	#if defined(HAVE_SLASHMACRO)
		leaq \var(%rip), \reg
	#elif defined(HAVE_DOLLARMACRO)
		leaq $0(%rip), $1
	#endif
#endif
.endm

#if defined(HAVE_SLASHMACRO)
	#define INCLUDE_FILE_PARM "\file"
#elif defined(HAVE_DOLLARMACRO)
	#define INCLUDE_FILE_PARM $0
#endif


.macro INCLUDE file
	.include  INCLUDE_FILE_PARM
.endm

/* include the file with the variable(s) if variable 'name' is not already included */
.macro INCLUDE_VAR_FILE file, name
	#if defined(HAVE_SLASHMACRO)
		.ifndef \name
			.include INCLUDE_FILE_PARM
		.endif
	#elif defined(HAVE_DOLLARMACRO)
		.ifndef $1
			.include INCLUDE_FILE_PARM
		.endif
	#endif
.endm

/* stupid helpers so we can have cpuid in one file */

.macro CPUID_PROLOGUE
#if (IS_X86_32)
	pushl %ebx
	pushl %esi
	pushl %edi
	pushl %ebp

	/* check that cpuid is supported */
	pushfl
	popl %eax
	movl %eax, %ecx
	xorl $(0x200000), %eax
	pushl %eax
	popfl
	pushfl
	popl %eax
	xorl %ecx, %eax
	shrl $(21), %eax
	andl $(1), %eax
	pushl %ecx
	popfl
	andl %eax, %eax
	jz Lcpuid_x86_done
#else
	pushq %rbx
	pushq %rsi
	pushq %rdi
	pushq %rbp
#endif
.endm

.macro CPUID_EPILOGUE
#if (IS_X86_32)
	popl %ebp
	popl %edi
	popl %esi
	popl %ebx
#else
	popq %rbp
	popq %rdi
	popq %rsi
	popq %rbx
#endif
	ret
.endm

.macro CPUCYCLES
	rdtsc
#if (IS_X86_64)
	shlq $(32), %rdx
	orq %rdx, %rax
#endif
	ret
.endm


/* Macros for CPUID only */

#define CPUID_GENERIC  (0     )
#define CPUID_X86      (1 << 0)
#define CPUID_MMX      (1 << 1)
#define CPUID_SSE      (1 << 2)
#define CPUID_SSE2     (1 << 3)
#define CPUID_SSE3     (1 << 4)
#define CPUID_SSSE3    (1 << 5)
#define CPUID_SSE4_1   (1 << 6)
#define CPUID_SSE4_2   (1 << 7)
#define CPUID_AVX      (1 << 8)
#define CPUID_XOP      (1 << 9)
#define CPUID_AVX2     (1 << 10)
#define CPUID_AVX512   (1 << 11)

#define CPUID_RDTSC     (1 << 25)
#define CPUID_RDRAND    (1 << 26)
#define CPUID_POPCNT    (1 << 27)
#define CPUID_FMA4      (1 << 28)
#define CPUID_FMA3      (1 << 29)
#define CPUID_PCLMULQDQ (1 << 30)
#define CPUID_AES       (1 << 31)

#endif /* BASE_GCC_X86_S */
