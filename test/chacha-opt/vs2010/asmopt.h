#ifndef ASMOPT_H
#define ASMOPT_H

#include <stddef.h>

/* Visual Studio with Yasm 1.2+ */
#define ARCH_X86
#define HAVE_AVX2
#define HAVE_AVX
#define HAVE_XOP
#define HAVE_SSE4_2
#define HAVE_SSE4_1
#define HAVE_SSSE3
#define HAVE_SSE3
#define HAVE_SSE2
#define HAVE_SSE
#define HAVE_MMX


#if (defined(_M_IX86))
	#define CPU_32BITS
#elif (defined(_M_X64))
	#define CPU_64BITS
#else
	#error This should never happen
#endif

#define HAVE_INT64
#define HAVE_INT32
#define HAVE_INT16
#define HAVE_INT8

#if (_MSC_VER < 1300)
	typedef signed __int64  int64_t; typedef unsigned __int64  uint64_t;
	typedef signed int      int32_t; typedef unsigned int      uint32_t;
	typedef signed short    int16_t; typedef unsigned short    uint16_t;
	typedef signed char      int8_t; typedef unsigned char      uint8_t;
#elif (_MSC_VER < 1600)
	typedef signed __int64  int64_t; typedef unsigned __int64  uint64_t;
	typedef signed __int32  int32_t; typedef unsigned __int32  uint32_t;
	typedef signed __int16  int16_t; typedef unsigned __int16  uint16_t;
	typedef signed __int8    int8_t; typedef unsigned __int8    uint8_t;
#else
	#include <stdint.h>
#endif

#endif /* ASMOPT_H */

