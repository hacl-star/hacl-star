#ifndef GCC_DRIVER_INC
#define GCC_DRIVER_INC

#include "asmopt_internal.h"

#if (defined(__i386__  ) || defined(__x86_64__))
	#include "x86/gcc.inc"
#endif

#if (defined(__arm__  ) || defined(__aarch64__))
	#include "arm/gcc.inc"
#endif

.macro INCLUDE_IF_X86_32BIT file
#if (IS_X86_32)
	.include INCLUDE_FILE_PARM
#endif
.endm

.macro INCLUDE_IF_X86_64BIT file
#if (IS_X86_64)
	.include INCLUDE_FILE_PARM
#endif
.endm


.macro INCLUDE_IF_MMX_32BIT file
#if defined(HAVE_MMX)
	INCLUDE_IF_X86_32BIT INCLUDE_FILE_PARM
#endif
.endm

.macro INCLUDE_IF_MMX_64BIT file
#if defined(HAVE_MMX)
	INCLUDE_IF_X86_64BIT INCLUDE_FILE_PARM
#endif
.endm


.macro INCLUDE_IF_SSE_32BIT file
#if defined(HAVE_SSE)
	INCLUDE_IF_X86_32BIT INCLUDE_FILE_PARM
#endif
.endm

.macro INCLUDE_IF_SSE_64BIT file
#if defined(HAVE_SSE)
	INCLUDE_IF_X86_64BIT INCLUDE_FILE_PARM
#endif
.endm


.macro INCLUDE_IF_SSE2_32BIT file
#if defined(HAVE_SSE2)
	INCLUDE_IF_X86_32BIT INCLUDE_FILE_PARM
#endif
.endm

.macro INCLUDE_IF_SSE2_64BIT file
#if defined(HAVE_SSE2)
	INCLUDE_IF_X86_64BIT INCLUDE_FILE_PARM
#endif
.endm


.macro INCLUDE_IF_SSE3_32BIT file
#if defined(HAVE_SSE3)
	INCLUDE_IF_X86_32BIT INCLUDE_FILE_PARM
#endif
.endm

.macro INCLUDE_IF_SSE3_64BIT file
#if defined(HAVE_SSE3)
	INCLUDE_IF_X86_64BIT INCLUDE_FILE_PARM
#endif
.endm


.macro INCLUDE_IF_SSSE3_32BIT file
#if defined(HAVE_SSSE3)
	INCLUDE_IF_X86_32BIT INCLUDE_FILE_PARM
#endif
.endm

.macro INCLUDE_IF_SSSE3_64BIT file
#if defined(HAVE_SSSE3)
	INCLUDE_IF_X86_64BIT INCLUDE_FILE_PARM
#endif
.endm


.macro INCLUDE_IF_SSE4_1_32BIT file
#if defined(HAVE_SSE4_1)
	INCLUDE_IF_X86_32BIT INCLUDE_FILE_PARM
#endif
.endm

.macro INCLUDE_IF_SSE4_1_64BIT file
#if defined(HAVE_SSE4_1)
	INCLUDE_IF_X86_64BIT INCLUDE_FILE_PARM
#endif
.endm


.macro INCLUDE_IF_SSE4_2_32BIT file
#if defined(HAVE_SSE4_2)
	INCLUDE_IF_X86_32BIT INCLUDE_FILE_PARM
#endif
.endm

.macro INCLUDE_IF_SSE4_2_64BIT file
#if defined(HAVE_SSE4_2)
	INCLUDE_IF_X86_64BIT INCLUDE_FILE_PARM
#endif
.endm


.macro INCLUDE_IF_AVX_32BIT file
#if defined(HAVE_AVX)
	INCLUDE_IF_X86_32BIT INCLUDE_FILE_PARM
#endif
.endm

.macro INCLUDE_IF_AVX_64BIT file
#if defined(HAVE_AVX)
	INCLUDE_IF_X86_64BIT INCLUDE_FILE_PARM
#endif
.endm


.macro INCLUDE_IF_XOP_32BIT file
#if defined(HAVE_XOP)
	INCLUDE_IF_X86_32BIT INCLUDE_FILE_PARM
#endif
.endm

.macro INCLUDE_IF_XOP_64BIT file
#if defined(HAVE_XOP)
	INCLUDE_IF_X86_64BIT INCLUDE_FILE_PARM
#endif
.endm


.macro INCLUDE_IF_AVX2_32BIT file
#if defined(HAVE_AVX2)
	INCLUDE_IF_X86_32BIT INCLUDE_FILE_PARM
#endif
.endm

.macro INCLUDE_IF_AVX2_64BIT file
#if defined(HAVE_AVX2)
	INCLUDE_IF_X86_64BIT INCLUDE_FILE_PARM
#endif
.endm


.macro INCLUDE_IF_AVX512_32BIT file
#if defined(HAVE_AVX512)
	INCLUDE_IF_X86_32BIT INCLUDE_FILE_PARM
#endif
.endm

.macro INCLUDE_IF_AVX512_64BIT file
#if defined(HAVE_AVX512)
	INCLUDE_IF_X86_64BIT INCLUDE_FILE_PARM
#endif
.endm

#endif /* GCC_DRIVER_INC */

