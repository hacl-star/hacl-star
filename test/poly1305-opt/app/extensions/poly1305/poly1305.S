#if defined(__GNUC__)
#include "gcc_driver.inc"
#else
;.if 0
%include "yasm_driver.inc"
;.endif
#endif

INCLUDE_IF_AVX2_64BIT "poly1305/poly1305_avx2-64.inc"
INCLUDE_IF_AVX_64BIT "poly1305/poly1305_avx-64.inc"
INCLUDE_IF_SSE2_64BIT "poly1305/poly1305_sse2-64.inc"
INCLUDE_IF_X86_64BIT "poly1305/poly1305_x86-64.inc"

INCLUDE_IF_AVX2_32BIT "poly1305/poly1305_avx2-32.inc"
INCLUDE_IF_AVX_32BIT "poly1305/poly1305_avx-32.inc"
INCLUDE_IF_SSE2_32BIT "poly1305/poly1305_sse2-32.inc"
INCLUDE_IF_X86_32BIT "poly1305/poly1305_x86-32.inc"

#if defined(HAVE_ARMv6)
#include "poly1305/poly1305_armv6-32.inc"
#endif

#if (defined(CPU_32BITS) && defined(HAVE_NEON))
#include "poly1305/poly1305_neon-32.inc"
#endif

