#if defined(__GNUC__)
#include "gcc_driver.inc"
#else
;.if 0
%include "yasm_driver.inc"
;.endif
#endif

INCLUDE_IF_AVX2_64BIT "chacha/chacha_avx2-64.inc"
INCLUDE_IF_XOP_64BIT "chacha/chacha_xop-64.inc"
INCLUDE_IF_AVX_64BIT "chacha/chacha_avx-64.inc"
INCLUDE_IF_SSSE3_64BIT "chacha/chacha_ssse3-64.inc"
INCLUDE_IF_SSE2_64BIT "chacha/chacha_sse2-64.inc"
INCLUDE_IF_X86_64BIT "chacha/chacha_x86-64.inc"

INCLUDE_IF_AVX2_32BIT "chacha/chacha_avx2-32.inc"
INCLUDE_IF_XOP_32BIT "chacha/chacha_xop-32.inc"
INCLUDE_IF_AVX_32BIT "chacha/chacha_avx-32.inc"
INCLUDE_IF_SSSE3_32BIT "chacha/chacha_ssse3-32.inc"
INCLUDE_IF_SSE2_32BIT "chacha/chacha_sse2-32.inc"
INCLUDE_IF_X86_32BIT "chacha/chacha_x86-32.inc"

#if defined(HAVE_ARMv6)
#include "chacha/chacha_armv6-32.inc"
#endif

#if (defined(CPU_32BITS) && defined(HAVE_NEON))
#include "chacha/chacha_neon-32.inc"
#endif

