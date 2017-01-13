#if defined(__GNUC__)
#include "gcc_driver.inc"
#else
;.if 0
%include "yasm_driver.inc"
;.endif
#endif

SECTION_TEXT

GLOBAL_LOCAL_PREFIX cpuid_x86
FN_LOCAL_PREFIX cpuid_x86
	CPUID_PROLOGUE

	/* use esi for flags */
	movl $(CPUID_X86), %esi

	/* cpuid 0 */
	movl $0, %eax
	xorl %ecx, %ecx
	cpuid

	/* eax = max level, store in edi */
	movl %eax, %edi

	/* cpus with >=2 cpuid levels support rdtsc */
	cmpl $2, %edi
	jb 1f
		orl $(CPUID_RDTSC), %esi
	1:

	testl $0x00000500, %edi
	jz Lcpuid_x86_notp5

		/* Intel P5 pre-B0, only MMX */
		orl $(CPUID_MMX), %esi
		jmp Lcpuid_x86_done

	Lcpuid_x86_notp5:

	/* cpuid 1 */
	movl $1, %eax
	xorl %ecx, %ecx
	cpuid

	/* rdrand */
	testl $(1 << 30), %ecx
	jz 1f
		orl $(CPUID_RDRAND), %esi
	1:

	/* aes */
	testl $(1 << 25), %ecx
	jz 1f
		orl $(CPUID_AES), %esi
	1:

	/* popcnt */
	testl $(1 << 23), %ecx
	jz 1f
		orl $(CPUID_POPCNT), %esi
	1:

	/* fma3 */
	testl $(1 << 12), %ecx
	jz 1f
		orl $(CPUID_FMA3), %esi
	1:

	/* pclmulqdq */
	testl $(1 << 1), %ecx
	jz 1f
		orl $(CPUID_PCLMULQDQ), %esi
	1:

	/* SSE4.2 */
	testl $(1 << 20), %ecx
	jz 1f
		orl $(CPUID_SSE4_2), %esi
	1:

	/* SSE4.1 */
	testl $(1 << 19), %ecx
	jz 1f
		orl $(CPUID_SSE4_1), %esi
	1:

	/* SSSE3 */
	testl $(1 << 9), %ecx
	jz 1f
		orl $(CPUID_SSSE3), %esi
	1:

	/* SSE3 */
	testl $(1     ), %ecx
	jz 1f
		orl $(CPUID_SSE3), %esi
	1:

	/* SSE2 */
	testl $(1 << 26), %edx
	jz 1f
		orl $(CPUID_SSE2), %esi
	1:

	/* SSE */
	testl $(1 << 25), %edx
	jz 1f
		orl $(CPUID_SSE), %esi
	1:

	/* MMX */
	testl $(1 << 23), %edx
	jz 1f
		orl $(CPUID_MMX), %esi
	1:

	/* test for xsave enabled by os */
	testl $(1 << 27), %ecx
	jz Lcpuid_x86_skipavxplus

	/* test for avx supported by cpu */
	testl $(1 << 28), %ecx
	jz Lcpuid_x86_skipavxplus

	/* xgetbv(0) */
	xorl %ecx, %ecx
	.byte 0x0f, 0x01, 0xd0

	/* save XCR0 in scratch(ebp) */
	movl %eax, %ebp

	/* XCR0 & (XMM | YMM) */
	andl $((1 << 2) | (1 << 1)), %eax
	cmpl $((1 << 2) | (1 << 1)), %eax
	jne Lcpuid_x86_skipavxplus

		/* AVX is ok to use */
		orl $(CPUID_AVX), %esi

		/* check for max level >= 7 */
		cmpl $7, %edi
		jb Lcpuid_x86_cpuid_below_7

			/* cpuid 7 */
			movl $7, %eax
			xorl %ecx, %ecx
			cpuid

			/* AVX2 */
			testl $(1 <<  5), %ebx
			jz 1f
				orl $(CPUID_AVX2), %esi
			1:

			/* XCR0 & (OPMASK | ZMMUPPER | ZMMEXTENDED) */
			andl $((1 << 5) | (1 << 6) | (1 << 7)), %ebp
			cmpl $((1 << 5) | (1 << 6) | (1 << 7)), %ebp
			jne Lcpuid_x86_skipavx512

				/* AVX-512 */
				testl $(1 << 16), %ebx
				jz 1f
					orl $(CPUID_AVX512), %esi
				1:

			Lcpuid_x86_skipavx512:

		Lcpuid_x86_cpuid_below_7:

		/* cpuid 0x80000000 */
		movl $0x80000000, %eax
		xorl %ecx, %ecx
		cpuid

		/* eax = max extended level  */
		cmpl $0x80000001, %eax
		jb Lcpuid_x86_skipxopplus

			/* cpuid $0x80000001 */
			movl $0x80000001, %eax
			xorl %ecx, %ecx
			cpuid

			/* fma4 */
			testl $(1 << 16), %ecx
			jz 1f
				orl $(CPUID_FMA4), %esi
			1:

			/* XOP */
			testl $(1 << 11), %ecx
			jz 1f
				orl $(CPUID_XOP), %esi
			1:

	Lcpuid_x86_skipxopplus:

	Lcpuid_x86_skipavxplus:

Lcpuid_x86_done:
	movl %esi, %eax

	CPUID_EPILOGUE
FN_END_LOCAL_PREFIX cpuid_x86



GLOBAL_LOCAL_PREFIX cpucycles_x86
FN_LOCAL_PREFIX cpucycles_x86

CPUCYCLES

FN_END_LOCAL_PREFIX cpucycles_x86
