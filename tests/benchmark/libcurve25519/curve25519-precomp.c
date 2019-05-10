/* SPDX-License-Identifier: GPL-2.0
 *
 * Copyright (c) 2017 Armando Faz <armfazh@ic.unicamp.br>. All Rights Reserved.
 * Copyright (C) 2018 Jason A. Donenfeld <Jason@zx2c4.com>. All Rights Reserved.
 * Copyright (C) 2018 Samuel Neves <sneves@dei.uc.pt>. All Rights Reserved.
 */

#include "libcurve25519_inline.h"

#include <stdint.h>
#include <stdbool.h>
#include <string.h>

typedef uint64_t u64;
typedef uint8_t u8;
typedef __uint128_t u128;

static inline u64 load64_le(const u8* b){
  uint64_t x;
  memcpy(&x, b, 8);
  return x;
}
static inline void store64_le(u8* b,u64 o) {
  memcpy(b,&o,8);
}

enum { CURVE25519_POINT_SIZE = 32 };

static __always_inline void normalize_secret(u8 secret[CURVE25519_POINT_SIZE])
{
	secret[0] &= 248;
	secret[31] &= 127;
	secret[31] |= 64;
}

enum { NUM_WORDS_ELTFP25519 = 4 };
typedef __attribute((aligned(32))) u64 eltfp25519_1w[NUM_WORDS_ELTFP25519];
typedef __attribute((aligned(32))) u64 eltfp25519_1w_buffer[2 * NUM_WORDS_ELTFP25519];

#define mul_eltfp25519_1w_adx(c, a, b) do { \
	mul_256x256_integer_adx(m.buffer, a, b); \
	red_eltfp25519_1w_adx(c, m.buffer); \
} while (0)

#define mul_eltfp25519_1w_bmi2(c, a, b) do { \
	mul_256x256_integer_bmi2(m.buffer, a, b); \
	red_eltfp25519_1w_bmi2(c, m.buffer); \
} while(0)

#define sqr_eltfp25519_1w_adx(a) do { \
	sqr_256x256_integer_adx(m.buffer, a); \
	red_eltfp25519_1w_adx(a, m.buffer); \
} while (0)

#define sqr_eltfp25519_1w_bmi2(a) do { \
	sqr_256x256_integer_bmi2(m.buffer, a); \
	red_eltfp25519_1w_bmi2(a, m.buffer); \
} while (0)

#define mul_eltfp25519_2w_adx(c, a, b) do { \
	mul2_256x256_integer_adx(m.buffer, a, b); \
	red_eltfp25519_2w_adx(c, m.buffer); \
} while (0)

#define mul_eltfp25519_2w_bmi2(c, a, b) do { \
	mul2_256x256_integer_bmi2(m.buffer, a, b); \
	red_eltfp25519_2w_bmi2(c, m.buffer); \
} while (0)

#define sqr_eltfp25519_2w_adx(a) do { \
	sqr2_256x256_integer_adx(m.buffer, a); \
	red_eltfp25519_2w_adx(a, m.buffer); \
} while (0)

#define sqr_eltfp25519_2w_bmi2(a) do { \
	sqr2_256x256_integer_bmi2(m.buffer, a); \
	red_eltfp25519_2w_bmi2(a, m.buffer); \
} while (0)

#define sqrn_eltfp25519_1w_adx(a, times) do { \
	int ____counter = (times); \
	while (____counter-- > 0) \
		sqr_eltfp25519_1w_adx(a); \
} while (0)

#define sqrn_eltfp25519_1w_bmi2(a, times) do { \
	int ____counter = (times); \
	while (____counter-- > 0) \
		sqr_eltfp25519_1w_bmi2(a); \
} while (0)

#define copy_eltfp25519_1w(C, A) do { \
	(C)[0] = (A)[0]; \
	(C)[1] = (A)[1]; \
	(C)[2] = (A)[2]; \
	(C)[3] = (A)[3]; \
} while (0)

#define setzero_eltfp25519_1w(C) do { \
	(C)[0] = 0; \
	(C)[1] = 0; \
	(C)[2] = 0; \
	(C)[3] = 0; \
} while (0)

/* c is two 512-bit products: c0[0:7]=a0[0:3]*b0[0:3] and c1[8:15]=a1[4:7]*b1[4:7]
 * a is two 256-bit integers: a0[0:3] and a1[4:7]
 * b is two 256-bit integers: b0[0:3] and b1[4:7]
 */
static void mul2_256x256_integer_adx(u64 *const c, const u64 *const a, const u64 *const b)
{
	asm volatile(
		"xorl %%r14d, %%r14d ;"
		"movq   (%1), %%rdx; "	/* A[0] */
		"mulx   (%2),  %%r8, %%r12; " /* A[0]*B[0] */
		"xorl %%r10d, %%r10d ;"
		"movq %%r8, (%0) ;"
		"mulx  8(%2), %%r10, %%rax; " /* A[0]*B[1] */
		"adox %%r10, %%r12 ;"
		"mulx 16(%2),  %%r8, %%rbx; " /* A[0]*B[2] */
		"adox  %%r8, %%rax ;"
		"mulx 24(%2), %%r10, %%rcx; " /* A[0]*B[3] */
		"adox %%r10, %%rbx ;"
		/******************************************/
		"adox %%r14, %%rcx ;"

		"movq  8(%1), %%rdx; "	/* A[1] */
		"mulx   (%2),  %%r8,  %%r9; " /* A[1]*B[0] */
		"adox %%r12,  %%r8 ;"
		"movq  %%r8, 8(%0) ;"
		"mulx  8(%2), %%r10, %%r11; " /* A[1]*B[1] */
		"adox %%r10,  %%r9 ;"
		"adcx  %%r9, %%rax ;"
		"mulx 16(%2),  %%r8, %%r13; " /* A[1]*B[2] */
		"adox  %%r8, %%r11 ;"
		"adcx %%r11, %%rbx ;"
		"mulx 24(%2), %%r10, %%r12; " /* A[1]*B[3] */
		"adox %%r10, %%r13 ;"
		"adcx %%r13, %%rcx ;"
		/******************************************/
		"adox %%r14, %%r12 ;"
		"adcx %%r14, %%r12 ;"

		"movq 16(%1), %%rdx; " /* A[2] */
		"xorl %%r10d, %%r10d ;"
		"mulx   (%2),  %%r8,  %%r9; " /* A[2]*B[0] */
		"adox %%rax,  %%r8 ;"
		"movq %%r8, 16(%0) ;"
		"mulx  8(%2), %%r10, %%r11; " /* A[2]*B[1] */
		"adox %%r10,  %%r9 ;"
		"adcx  %%r9, %%rbx ;"
		"mulx 16(%2),  %%r8, %%r13; " /* A[2]*B[2] */
		"adox  %%r8, %%r11 ;"
		"adcx %%r11, %%rcx ;"
		"mulx 24(%2), %%r10, %%rax; " /* A[2]*B[3] */
		"adox %%r10, %%r13 ;"
		"adcx %%r13, %%r12 ;"
		/******************************************/
		"adox %%r14, %%rax ;"
		"adcx %%r14, %%rax ;"

		"movq 24(%1), %%rdx; " /* A[3] */
		"xorl %%r10d, %%r10d ;"
		"mulx   (%2),  %%r8,  %%r9; " /* A[3]*B[0] */
		"adox %%rbx,  %%r8 ;"
		"movq %%r8, 24(%0) ;"
		"mulx  8(%2), %%r10, %%r11; " /* A[3]*B[1] */
		"adox %%r10,  %%r9 ;"
		"adcx  %%r9, %%rcx ;"
		"movq %%rcx, 32(%0) ;"
		"mulx 16(%2),  %%r8, %%r13; " /* A[3]*B[2] */
		"adox  %%r8, %%r11 ;"
		"adcx %%r11, %%r12 ;"
		"movq %%r12, 40(%0) ;"
		"mulx 24(%2), %%r10, %%rbx; " /* A[3]*B[3] */
		"adox %%r10, %%r13 ;"
		"adcx %%r13, %%rax ;"
		"movq %%rax, 48(%0) ;"
		/******************************************/
		"adox %%r14, %%rbx ;"
		"adcx %%r14, %%rbx ;"
		"movq %%rbx, 56(%0) ;"

		"movq 32(%1), %%rdx; "	/* C[0] */
		"mulx 32(%2),  %%r8, %%r12; " /* C[0]*D[0] */
		"xorl %%r10d, %%r10d ;"
		"movq %%r8, 64(%0);"
		"mulx 40(%2), %%r10, %%rax; " /* C[0]*D[1] */
		"adox %%r10, %%r12 ;"
		"mulx 48(%2),  %%r8, %%rbx; " /* C[0]*D[2] */
		"adox  %%r8, %%rax ;"
		"mulx 56(%2), %%r10, %%rcx; " /* C[0]*D[3] */
		"adox %%r10, %%rbx ;"
		/******************************************/
		"adox %%r14, %%rcx ;"

		"movq 40(%1), %%rdx; " /* C[1] */
		"xorl %%r10d, %%r10d ;"
		"mulx 32(%2),  %%r8,  %%r9; " /* C[1]*D[0] */
		"adox %%r12,  %%r8 ;"
		"movq  %%r8, 72(%0);"
		"mulx 40(%2), %%r10, %%r11; " /* C[1]*D[1] */
		"adox %%r10,  %%r9 ;"
		"adcx  %%r9, %%rax ;"
		"mulx 48(%2),  %%r8, %%r13; " /* C[1]*D[2] */
		"adox  %%r8, %%r11 ;"
		"adcx %%r11, %%rbx ;"
		"mulx 56(%2), %%r10, %%r12; " /* C[1]*D[3] */
		"adox %%r10, %%r13 ;"
		"adcx %%r13, %%rcx ;"
		/******************************************/
		"adox %%r14, %%r12 ;"
		"adcx %%r14, %%r12 ;"

		"movq 48(%1), %%rdx; " /* C[2] */
		"xorl %%r10d, %%r10d ;"
		"mulx 32(%2),  %%r8,  %%r9; " /* C[2]*D[0] */
		"adox %%rax,  %%r8 ;"
		"movq  %%r8, 80(%0);"
		"mulx 40(%2), %%r10, %%r11; " /* C[2]*D[1] */
		"adox %%r10,  %%r9 ;"
		"adcx  %%r9, %%rbx ;"
		"mulx 48(%2),  %%r8, %%r13; " /* C[2]*D[2] */
		"adox  %%r8, %%r11 ;"
		"adcx %%r11, %%rcx ;"
		"mulx 56(%2), %%r10, %%rax; " /* C[2]*D[3] */
		"adox %%r10, %%r13 ;"
		"adcx %%r13, %%r12 ;"
		/******************************************/
		"adox %%r14, %%rax ;"
		"adcx %%r14, %%rax ;"

		"movq 56(%1), %%rdx; " /* C[3] */
		"xorl %%r10d, %%r10d ;"
		"mulx 32(%2),  %%r8,  %%r9; " /* C[3]*D[0] */
		"adox %%rbx,  %%r8 ;"
		"movq  %%r8, 88(%0);"
		"mulx 40(%2), %%r10, %%r11; " /* C[3]*D[1] */
		"adox %%r10,  %%r9 ;"
		"adcx  %%r9, %%rcx ;"
		"movq %%rcx,  96(%0) ;"
		"mulx 48(%2),  %%r8, %%r13; " /* C[3]*D[2] */
		"adox  %%r8, %%r11 ;"
		"adcx %%r11, %%r12 ;"
		"movq %%r12, 104(%0) ;"
		"mulx 56(%2), %%r10, %%rbx; " /* C[3]*D[3] */
		"adox %%r10, %%r13 ;"
		"adcx %%r13, %%rax ;"
		"movq %%rax, 112(%0) ;"
		/******************************************/
		"adox %%r14, %%rbx ;"
		"adcx %%r14, %%rbx ;"
		"movq %%rbx, 120(%0) ;"
		:
		: "r"(c), "r"(a), "r"(b)
		: "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14");
}

static void mul2_256x256_integer_bmi2(u64 *const c, const u64 *const a, const u64 *const b)
{
	asm volatile(
		"movq   (%1), %%rdx; "	/* A[0] */
		"mulx   (%2),  %%r8, %%r12; " /* A[0]*B[0] */
		"movq %%r8,  (%0) ;"
		"mulx  8(%2), %%r10, %%rax; " /* A[0]*B[1] */
		"addq %%r10, %%r12 ;"
		"mulx 16(%2),  %%r8, %%rbx; " /* A[0]*B[2] */
		"adcq  %%r8, %%rax ;"
		"mulx 24(%2), %%r10, %%rcx; " /* A[0]*B[3] */
		"adcq %%r10, %%rbx ;"
		/******************************************/
		"adcq    $0, %%rcx ;"

		"movq  8(%1), %%rdx; "	/* A[1] */
		"mulx   (%2),  %%r8,  %%r9; " /* A[1]*B[0] */
		"addq %%r12,  %%r8 ;"
		"movq %%r8, 8(%0) ;"
		"mulx  8(%2), %%r10, %%r11; " /* A[1]*B[1] */
		"adcq %%r10,  %%r9 ;"
		"mulx 16(%2),  %%r8, %%r13; " /* A[1]*B[2] */
		"adcq  %%r8, %%r11 ;"
		"mulx 24(%2), %%r10, %%r12; " /* A[1]*B[3] */
		"adcq %%r10, %%r13 ;"
		/******************************************/
		"adcq    $0, %%r12 ;"

		"addq  %%r9, %%rax ;"
		"adcq %%r11, %%rbx ;"
		"adcq %%r13, %%rcx ;"
		"adcq    $0, %%r12 ;"

		"movq 16(%1), %%rdx; "	/* A[2] */
		"mulx   (%2),  %%r8,  %%r9; " /* A[2]*B[0] */
		"addq %%rax,  %%r8 ;"
		"movq %%r8, 16(%0) ;"
		"mulx  8(%2), %%r10, %%r11; " /* A[2]*B[1] */
		"adcq %%r10,  %%r9 ;"
		"mulx 16(%2),  %%r8, %%r13; " /* A[2]*B[2] */
		"adcq  %%r8, %%r11 ;"
		"mulx 24(%2), %%r10, %%rax; " /* A[2]*B[3] */
		"adcq %%r10, %%r13 ;"
		/******************************************/
		"adcq    $0, %%rax ;"

		"addq  %%r9, %%rbx ;"
		"adcq %%r11, %%rcx ;"
		"adcq %%r13, %%r12 ;"
		"adcq    $0, %%rax ;"

		"movq 24(%1), %%rdx; "	/* A[3] */
		"mulx   (%2),  %%r8,  %%r9; " /* A[3]*B[0] */
		"addq %%rbx,  %%r8 ;"
		"movq %%r8, 24(%0) ;"
		"mulx  8(%2), %%r10, %%r11; " /* A[3]*B[1] */
		"adcq %%r10,  %%r9 ;"
		"mulx 16(%2),  %%r8, %%r13; " /* A[3]*B[2] */
		"adcq  %%r8, %%r11 ;"
		"mulx 24(%2), %%r10, %%rbx; " /* A[3]*B[3] */
		"adcq %%r10, %%r13 ;"
		/******************************************/
		"adcq    $0, %%rbx ;"

		"addq  %%r9, %%rcx ;"
		"movq %%rcx, 32(%0) ;"
		"adcq %%r11, %%r12 ;"
		"movq %%r12, 40(%0) ;"
		"adcq %%r13, %%rax ;"
		"movq %%rax, 48(%0) ;"
		"adcq    $0, %%rbx ;"
		"movq %%rbx, 56(%0) ;"

		"movq 32(%1), %%rdx; "	/* C[0] */
		"mulx 32(%2),  %%r8, %%r12; " /* C[0]*D[0] */
		"movq %%r8, 64(%0) ;"
		"mulx 40(%2), %%r10, %%rax; " /* C[0]*D[1] */
		"addq %%r10, %%r12 ;"
		"mulx 48(%2),  %%r8, %%rbx; " /* C[0]*D[2] */
		"adcq  %%r8, %%rax ;"
		"mulx 56(%2), %%r10, %%rcx; " /* C[0]*D[3] */
		"adcq %%r10, %%rbx ;"
		/******************************************/
		"adcq    $0, %%rcx ;"

		"movq 40(%1), %%rdx; "	/* C[1] */
		"mulx 32(%2),  %%r8,  %%r9; " /* C[1]*D[0] */
		"addq %%r12,  %%r8 ;"
		"movq %%r8, 72(%0) ;"
		"mulx 40(%2), %%r10, %%r11; " /* C[1]*D[1] */
		"adcq %%r10,  %%r9 ;"
		"mulx 48(%2),  %%r8, %%r13; " /* C[1]*D[2] */
		"adcq  %%r8, %%r11 ;"
		"mulx 56(%2), %%r10, %%r12; " /* C[1]*D[3] */
		"adcq %%r10, %%r13 ;"
		/******************************************/
		"adcq    $0, %%r12 ;"

		"addq  %%r9, %%rax ;"
		"adcq %%r11, %%rbx ;"
		"adcq %%r13, %%rcx ;"
		"adcq    $0, %%r12 ;"

		"movq 48(%1), %%rdx; "	/* C[2] */
		"mulx 32(%2),  %%r8,  %%r9; " /* C[2]*D[0] */
		"addq %%rax,  %%r8 ;"
		"movq %%r8, 80(%0) ;"
		"mulx 40(%2), %%r10, %%r11; " /* C[2]*D[1] */
		"adcq %%r10,  %%r9 ;"
		"mulx 48(%2),  %%r8, %%r13; " /* C[2]*D[2] */
		"adcq  %%r8, %%r11 ;"
		"mulx 56(%2), %%r10, %%rax; " /* C[2]*D[3] */
		"adcq %%r10, %%r13 ;"
		/******************************************/
		"adcq    $0, %%rax ;"

		"addq  %%r9, %%rbx ;"
		"adcq %%r11, %%rcx ;"
		"adcq %%r13, %%r12 ;"
		"adcq    $0, %%rax ;"

		"movq 56(%1), %%rdx; "	/* C[3] */
		"mulx 32(%2),  %%r8,  %%r9; " /* C[3]*D[0] */
		"addq %%rbx,  %%r8 ;"
		"movq %%r8, 88(%0) ;"
		"mulx 40(%2), %%r10, %%r11; " /* C[3]*D[1] */
		"adcq %%r10,  %%r9 ;"
		"mulx 48(%2),  %%r8, %%r13; " /* C[3]*D[2] */
		"adcq  %%r8, %%r11 ;"
		"mulx 56(%2), %%r10, %%rbx; " /* C[3]*D[3] */
		"adcq %%r10, %%r13 ;"
		/******************************************/
		"adcq    $0, %%rbx ;"

		"addq  %%r9, %%rcx ;"
		"movq %%rcx,  96(%0) ;"
		"adcq %%r11, %%r12 ;"
		"movq %%r12, 104(%0) ;"
		"adcq %%r13, %%rax ;"
		"movq %%rax, 112(%0) ;"
		"adcq    $0, %%rbx ;"
		"movq %%rbx, 120(%0) ;"
		:
		: "r"(c), "r"(a), "r"(b)
		: "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13");
}

static void sqr2_256x256_integer_adx(u64 *const c, const u64 *const a)
{
	asm volatile(
		"movq   (%1), %%rdx        ;" /* A[0]      */
		"mulx  8(%1),  %%r8, %%r14 ;" /* A[1]*A[0] */
		"xorl %%r15d, %%r15d;"
		"mulx 16(%1),  %%r9, %%r10 ;" /* A[2]*A[0] */
		"adcx %%r14,  %%r9 ;"
		"mulx 24(%1), %%rax, %%rcx ;" /* A[3]*A[0] */
		"adcx %%rax, %%r10 ;"
		"movq 24(%1), %%rdx        ;" /* A[3]      */
		"mulx  8(%1), %%r11, %%r12 ;" /* A[1]*A[3] */
		"adcx %%rcx, %%r11 ;"
		"mulx 16(%1), %%rax, %%r13 ;" /* A[2]*A[3] */
		"adcx %%rax, %%r12 ;"
		"movq  8(%1), %%rdx        ;" /* A[1]      */
		"adcx %%r15, %%r13 ;"
		"mulx 16(%1), %%rax, %%rcx ;" /* A[2]*A[1] */
		"movq    $0, %%r14 ;"
		/******************************************/
		"adcx %%r15, %%r14 ;"

		"xorl %%r15d, %%r15d;"
		"adox %%rax, %%r10 ;"
		"adcx  %%r8,  %%r8 ;"
		"adox %%rcx, %%r11 ;"
		"adcx  %%r9,  %%r9 ;"
		"adox %%r15, %%r12 ;"
		"adcx %%r10, %%r10 ;"
		"adox %%r15, %%r13 ;"
		"adcx %%r11, %%r11 ;"
		"adox %%r15, %%r14 ;"
		"adcx %%r12, %%r12 ;"
		"adcx %%r13, %%r13 ;"
		"adcx %%r14, %%r14 ;"

		"movq   (%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ;" /* A[0]^2 */
		/*******************/
		"movq %%rax,  0(%0) ;"
		"addq %%rcx,  %%r8 ;"
		"movq  %%r8,  8(%0) ;"
		"movq  8(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ;" /* A[1]^2 */
		"adcq %%rax,  %%r9 ;"
		"movq  %%r9, 16(%0) ;"
		"adcq %%rcx, %%r10 ;"
		"movq %%r10, 24(%0) ;"
		"movq 16(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ;" /* A[2]^2 */
		"adcq %%rax, %%r11 ;"
		"movq %%r11, 32(%0) ;"
		"adcq %%rcx, %%r12 ;"
		"movq %%r12, 40(%0) ;"
		"movq 24(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ;" /* A[3]^2 */
		"adcq %%rax, %%r13 ;"
		"movq %%r13, 48(%0) ;"
		"adcq %%rcx, %%r14 ;"
		"movq %%r14, 56(%0) ;"


		"movq 32(%1), %%rdx        ;" /* B[0]      */
		"mulx 40(%1),  %%r8, %%r14 ;" /* B[1]*B[0] */
		"xorl %%r15d, %%r15d;"
		"mulx 48(%1),  %%r9, %%r10 ;" /* B[2]*B[0] */
		"adcx %%r14,  %%r9 ;"
		"mulx 56(%1), %%rax, %%rcx ;" /* B[3]*B[0] */
		"adcx %%rax, %%r10 ;"
		"movq 56(%1), %%rdx        ;" /* B[3]      */
		"mulx 40(%1), %%r11, %%r12 ;" /* B[1]*B[3] */
		"adcx %%rcx, %%r11 ;"
		"mulx 48(%1), %%rax, %%r13 ;" /* B[2]*B[3] */
		"adcx %%rax, %%r12 ;"
		"movq 40(%1), %%rdx        ;" /* B[1]      */
		"adcx %%r15, %%r13 ;"
		"mulx 48(%1), %%rax, %%rcx ;" /* B[2]*B[1] */
		"movq    $0, %%r14 ;"
		/******************************************/
		"adcx %%r15, %%r14 ;"

		"xorl %%r15d, %%r15d;"
		"adox %%rax, %%r10 ;"
		"adcx  %%r8,  %%r8 ;"
		"adox %%rcx, %%r11 ;"
		"adcx  %%r9,  %%r9 ;"
		"adox %%r15, %%r12 ;"
		"adcx %%r10, %%r10 ;"
		"adox %%r15, %%r13 ;"
		"adcx %%r11, %%r11 ;"
		"adox %%r15, %%r14 ;"
		"adcx %%r12, %%r12 ;"
		"adcx %%r13, %%r13 ;"
		"adcx %%r14, %%r14 ;"

		"movq 32(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ;" /* B[0]^2 */
		/*******************/
		"movq %%rax,  64(%0) ;"
		"addq %%rcx,  %%r8 ;"
		"movq  %%r8,  72(%0) ;"
		"movq 40(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ;" /* B[1]^2 */
		"adcq %%rax,  %%r9 ;"
		"movq  %%r9,  80(%0) ;"
		"adcq %%rcx, %%r10 ;"
		"movq %%r10,  88(%0) ;"
		"movq 48(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ;" /* B[2]^2 */
		"adcq %%rax, %%r11 ;"
		"movq %%r11,  96(%0) ;"
		"adcq %%rcx, %%r12 ;"
		"movq %%r12, 104(%0) ;"
		"movq 56(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ;" /* B[3]^2 */
		"adcq %%rax, %%r13 ;"
		"movq %%r13, 112(%0) ;"
		"adcq %%rcx, %%r14 ;"
		"movq %%r14, 120(%0) ;"
		:
		: "r"(c), "r"(a)
		: "memory", "cc", "%rax", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15");
}

static void sqr2_256x256_integer_bmi2(u64 *const c, const u64 *const a)
{
	asm volatile(
		"movq  8(%1), %%rdx        ;" /* A[1]      */
		"mulx   (%1),  %%r8,  %%r9 ;" /* A[0]*A[1] */
		"mulx 16(%1), %%r10, %%r11 ;" /* A[2]*A[1] */
		"mulx 24(%1), %%rcx, %%r14 ;" /* A[3]*A[1] */

		"movq 16(%1), %%rdx        ;" /* A[2]      */
		"mulx 24(%1), %%r12, %%r13 ;" /* A[3]*A[2] */
		"mulx   (%1), %%rax, %%rdx ;" /* A[0]*A[2] */

		"addq %%rax,  %%r9 ;"
		"adcq %%rdx, %%r10 ;"
		"adcq %%rcx, %%r11 ;"
		"adcq %%r14, %%r12 ;"
		"adcq    $0, %%r13 ;"
		"movq    $0, %%r14 ;"
		"adcq    $0, %%r14 ;"

		"movq   (%1), %%rdx        ;" /* A[0]      */
		"mulx 24(%1), %%rax, %%rcx ;" /* A[0]*A[3] */

		"addq %%rax, %%r10 ;"
		"adcq %%rcx, %%r11 ;"
		"adcq    $0, %%r12 ;"
		"adcq    $0, %%r13 ;"
		"adcq    $0, %%r14 ;"

		"shldq $1, %%r13, %%r14 ;"
		"shldq $1, %%r12, %%r13 ;"
		"shldq $1, %%r11, %%r12 ;"
		"shldq $1, %%r10, %%r11 ;"
		"shldq $1,  %%r9, %%r10 ;"
		"shldq $1,  %%r8,  %%r9 ;"
		"shlq  $1,  %%r8        ;"

		/*******************/
		"mulx %%rdx, %%rax, %%rcx ; " /* A[0]^2 */
		/*******************/
		"movq %%rax,  0(%0) ;"
		"addq %%rcx,  %%r8 ;"
		"movq  %%r8,  8(%0) ;"
		"movq  8(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ; " /* A[1]^2 */
		"adcq %%rax,  %%r9 ;"
		"movq  %%r9, 16(%0) ;"
		"adcq %%rcx, %%r10 ;"
		"movq %%r10, 24(%0) ;"
		"movq 16(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ; " /* A[2]^2 */
		"adcq %%rax, %%r11 ;"
		"movq %%r11, 32(%0) ;"
		"adcq %%rcx, %%r12 ;"
		"movq %%r12, 40(%0) ;"
		"movq 24(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ; " /* A[3]^2 */
		"adcq %%rax, %%r13 ;"
		"movq %%r13, 48(%0) ;"
		"adcq %%rcx, %%r14 ;"
		"movq %%r14, 56(%0) ;"

		"movq 40(%1), %%rdx        ;" /* B[1]      */
		"mulx 32(%1),  %%r8,  %%r9 ;" /* B[0]*B[1] */
		"mulx 48(%1), %%r10, %%r11 ;" /* B[2]*B[1] */
		"mulx 56(%1), %%rcx, %%r14 ;" /* B[3]*B[1] */

		"movq 48(%1), %%rdx        ;" /* B[2]      */
		"mulx 56(%1), %%r12, %%r13 ;" /* B[3]*B[2] */
		"mulx 32(%1), %%rax, %%rdx ;" /* B[0]*B[2] */

		"addq %%rax,  %%r9 ;"
		"adcq %%rdx, %%r10 ;"
		"adcq %%rcx, %%r11 ;"
		"adcq %%r14, %%r12 ;"
		"adcq    $0, %%r13 ;"
		"movq    $0, %%r14 ;"
		"adcq    $0, %%r14 ;"

		"movq 32(%1), %%rdx        ;" /* B[0]      */
		"mulx 56(%1), %%rax, %%rcx ;" /* B[0]*B[3] */

		"addq %%rax, %%r10 ;"
		"adcq %%rcx, %%r11 ;"
		"adcq    $0, %%r12 ;"
		"adcq    $0, %%r13 ;"
		"adcq    $0, %%r14 ;"

		"shldq $1, %%r13, %%r14 ;"
		"shldq $1, %%r12, %%r13 ;"
		"shldq $1, %%r11, %%r12 ;"
		"shldq $1, %%r10, %%r11 ;"
		"shldq $1,  %%r9, %%r10 ;"
		"shldq $1,  %%r8,  %%r9 ;"
		"shlq  $1,  %%r8        ;"

		/*******************/
		"mulx %%rdx, %%rax, %%rcx ; " /* B[0]^2 */
		/*******************/
		"movq %%rax,  64(%0) ;"
		"addq %%rcx,  %%r8 ;"
		"movq  %%r8,  72(%0) ;"
		"movq 40(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ; " /* B[1]^2 */
		"adcq %%rax,  %%r9 ;"
		"movq  %%r9,  80(%0) ;"
		"adcq %%rcx, %%r10 ;"
		"movq %%r10,  88(%0) ;"
		"movq 48(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ; " /* B[2]^2 */
		"adcq %%rax, %%r11 ;"
		"movq %%r11,  96(%0) ;"
		"adcq %%rcx, %%r12 ;"
		"movq %%r12, 104(%0) ;"
		"movq 56(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ; " /* B[3]^2 */
		"adcq %%rax, %%r13 ;"
		"movq %%r13, 112(%0) ;"
		"adcq %%rcx, %%r14 ;"
		"movq %%r14, 120(%0) ;"
		:
		: "r"(c), "r"(a)
		: "memory", "cc", "%rax", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14");
}

static void red_eltfp25519_2w_adx(u64 *const c, const u64 *const a)
{
	asm volatile(
		"movl    $38, %%edx; "	/* 2*c = 38 = 2^256 */
		"mulx 32(%1),  %%r8, %%r10; " /* c*C[4] */
		"xorl %%ebx, %%ebx ;"
		"adox   (%1),  %%r8 ;"
		"mulx 40(%1),  %%r9, %%r11; " /* c*C[5] */
		"adcx %%r10,  %%r9 ;"
		"adox  8(%1),  %%r9 ;"
		"mulx 48(%1), %%r10, %%rax; " /* c*C[6] */
		"adcx %%r11, %%r10 ;"
		"adox 16(%1), %%r10 ;"
		"mulx 56(%1), %%r11, %%rcx; " /* c*C[7] */
		"adcx %%rax, %%r11 ;"
		"adox 24(%1), %%r11 ;"
		/***************************************/
		"adcx %%rbx, %%rcx ;"
		"adox  %%rbx, %%rcx ;"
		"imul %%rdx, %%rcx ;" /* c*C[4], cf=0, of=0 */
		"adcx %%rcx,  %%r8 ;"
		"adcx %%rbx,  %%r9 ;"
		"movq  %%r9,  8(%0) ;"
		"adcx %%rbx, %%r10 ;"
		"movq %%r10, 16(%0) ;"
		"adcx %%rbx, %%r11 ;"
		"movq %%r11, 24(%0) ;"
		"mov     $0, %%ecx ;"
		"cmovc %%edx, %%ecx ;"
		"addq %%rcx,  %%r8 ;"
		"movq  %%r8,   (%0) ;"

		"mulx  96(%1),  %%r8, %%r10; " /* c*C[4] */
		"xorl %%ebx, %%ebx ;"
		"adox 64(%1),  %%r8 ;"
		"mulx 104(%1),  %%r9, %%r11; " /* c*C[5] */
		"adcx %%r10,  %%r9 ;"
		"adox 72(%1),  %%r9 ;"
		"mulx 112(%1), %%r10, %%rax; " /* c*C[6] */
		"adcx %%r11, %%r10 ;"
		"adox 80(%1), %%r10 ;"
		"mulx 120(%1), %%r11, %%rcx; " /* c*C[7] */
		"adcx %%rax, %%r11 ;"
		"adox 88(%1), %%r11 ;"
		/****************************************/
		"adcx %%rbx, %%rcx ;"
		"adox  %%rbx, %%rcx ;"
		"imul %%rdx, %%rcx ;" /* c*C[4], cf=0, of=0 */
		"adcx %%rcx,  %%r8 ;"
		"adcx %%rbx,  %%r9 ;"
		"movq  %%r9, 40(%0) ;"
		"adcx %%rbx, %%r10 ;"
		"movq %%r10, 48(%0) ;"
		"adcx %%rbx, %%r11 ;"
		"movq %%r11, 56(%0) ;"
		"mov     $0, %%ecx ;"
		"cmovc %%edx, %%ecx ;"
		"addq %%rcx,  %%r8 ;"
		"movq  %%r8, 32(%0) ;"
		:
		: "r"(c), "r"(a)
		: "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11");
}

static void red_eltfp25519_2w_bmi2(u64 *const c, const u64 *const a)
{
	asm volatile(
		"movl    $38, %%edx ; "       /* 2*c = 38 = 2^256 */
		"mulx 32(%1),  %%r8, %%r10 ;" /* c*C[4] */
		"mulx 40(%1),  %%r9, %%r11 ;" /* c*C[5] */
		"addq %%r10,  %%r9 ;"
		"mulx 48(%1), %%r10, %%rax ;" /* c*C[6] */
		"adcq %%r11, %%r10 ;"
		"mulx 56(%1), %%r11, %%rcx ;" /* c*C[7] */
		"adcq %%rax, %%r11 ;"
		/***************************************/
		"adcq    $0, %%rcx ;"
		"addq   (%1),  %%r8 ;"
		"adcq  8(%1),  %%r9 ;"
		"adcq 16(%1), %%r10 ;"
		"adcq 24(%1), %%r11 ;"
		"adcq     $0, %%rcx ;"
		"imul %%rdx, %%rcx ;" /* c*C[4], cf=0 */
		"addq %%rcx,  %%r8 ;"
		"adcq    $0,  %%r9 ;"
		"movq  %%r9,  8(%0) ;"
		"adcq    $0, %%r10 ;"
		"movq %%r10, 16(%0) ;"
		"adcq    $0, %%r11 ;"
		"movq %%r11, 24(%0) ;"
		"mov     $0, %%ecx ;"
		"cmovc %%edx, %%ecx ;"
		"addq %%rcx,  %%r8 ;"
		"movq  %%r8,   (%0) ;"

		"mulx  96(%1),  %%r8, %%r10 ;" /* c*C[4] */
		"mulx 104(%1),  %%r9, %%r11 ;" /* c*C[5] */
		"addq %%r10,  %%r9 ;"
		"mulx 112(%1), %%r10, %%rax ;" /* c*C[6] */
		"adcq %%r11, %%r10 ;"
		"mulx 120(%1), %%r11, %%rcx ;" /* c*C[7] */
		"adcq %%rax, %%r11 ;"
		/****************************************/
		"adcq    $0, %%rcx ;"
		"addq 64(%1),  %%r8 ;"
		"adcq 72(%1),  %%r9 ;"
		"adcq 80(%1), %%r10 ;"
		"adcq 88(%1), %%r11 ;"
		"adcq     $0, %%rcx ;"
		"imul %%rdx, %%rcx ;" /* c*C[4], cf=0 */
		"addq %%rcx,  %%r8 ;"
		"adcq    $0,  %%r9 ;"
		"movq  %%r9, 40(%0) ;"
		"adcq    $0, %%r10 ;"
		"movq %%r10, 48(%0) ;"
		"adcq    $0, %%r11 ;"
		"movq %%r11, 56(%0) ;"
		"mov     $0, %%ecx ;"
		"cmovc %%edx, %%ecx ;"
		"addq %%rcx,  %%r8 ;"
		"movq  %%r8, 32(%0) ;"
		:
		: "r"(c), "r"(a)
		: "memory", "cc", "%rax", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11");
}

static void mul_256x256_integer_adx(u64 *const c, const u64 *const a, const u64 *const b)
{
	asm volatile(
		"movq   (%1), %%rdx; "	/* A[0] */
		"mulx   (%2),  %%r8,  %%r9; " /* A[0]*B[0] */
		"xorl %%r10d, %%r10d ;"
		"movq  %%r8,  (%0) ;"
		"mulx  8(%2), %%r10, %%r11; " /* A[0]*B[1] */
		"adox  %%r9, %%r10 ;"
		"movq %%r10, 8(%0) ;"
		"mulx 16(%2), %%r12, %%r13; " /* A[0]*B[2] */
		"adox %%r11, %%r12 ;"
		"mulx 24(%2), %%r14, %%rdx; " /* A[0]*B[3] */
		"adox %%r13, %%r14 ;"
		"movq $0, %%rax ;"
		/******************************************/
		"adox %%rdx, %%rax ;"

		"movq  8(%1), %%rdx; "	/* A[1] */
		"mulx   (%2),  %%r8,  %%r9; " /* A[1]*B[0] */
		"xorl %%r10d, %%r10d ;"
		"adcx 8(%0),  %%r8 ;"
		"movq  %%r8,  8(%0) ;"
		"mulx  8(%2), %%r10, %%r11; " /* A[1]*B[1] */
		"adox  %%r9, %%r10 ;"
		"adcx %%r12, %%r10 ;"
		"movq %%r10, 16(%0) ;"
		"mulx 16(%2), %%r12, %%r13; " /* A[1]*B[2] */
		"adox %%r11, %%r12 ;"
		"adcx %%r14, %%r12 ;"
		"movq $0, %%r8  ;"
		"mulx 24(%2), %%r14, %%rdx; " /* A[1]*B[3] */
		"adox %%r13, %%r14 ;"
		"adcx %%rax, %%r14 ;"
		"movq $0, %%rax ;"
		/******************************************/
		"adox %%rdx, %%rax ;"
		"adcx  %%r8, %%rax ;"

		"movq 16(%1), %%rdx; "	/* A[2] */
		"mulx   (%2),  %%r8,  %%r9; " /* A[2]*B[0] */
		"xorl %%r10d, %%r10d ;"
		"adcx 16(%0), %%r8 ;"
		"movq  %%r8, 16(%0) ;"
		"mulx  8(%2), %%r10, %%r11; " /* A[2]*B[1] */
		"adox  %%r9, %%r10 ;"
		"adcx %%r12, %%r10 ;"
		"movq %%r10, 24(%0) ;"
		"mulx 16(%2), %%r12, %%r13; " /* A[2]*B[2] */
		"adox %%r11, %%r12 ;"
		"adcx %%r14, %%r12 ;"
		"movq $0, %%r8  ;"
		"mulx 24(%2), %%r14, %%rdx; " /* A[2]*B[3] */
		"adox %%r13, %%r14 ;"
		"adcx %%rax, %%r14 ;"
		"movq $0, %%rax ;"
		/******************************************/
		"adox %%rdx, %%rax ;"
		"adcx  %%r8, %%rax ;"

		"movq 24(%1), %%rdx; "	/* A[3] */
		"mulx   (%2),  %%r8,  %%r9; " /* A[3]*B[0] */
		"xorl %%r10d, %%r10d ;"
		"adcx 24(%0), %%r8 ;"
		"movq  %%r8, 24(%0) ;"
		"mulx  8(%2), %%r10, %%r11; " /* A[3]*B[1] */
		"adox  %%r9, %%r10 ;"
		"adcx %%r12, %%r10 ;"
		"movq %%r10, 32(%0) ;"
		"mulx 16(%2), %%r12, %%r13; " /* A[3]*B[2] */
		"adox %%r11, %%r12 ;"
		"adcx %%r14, %%r12 ;"
		"movq %%r12, 40(%0) ;"
		"movq $0, %%r8  ;"
		"mulx 24(%2), %%r14, %%rdx; " /* A[3]*B[3] */
		"adox %%r13, %%r14 ;"
		"adcx %%rax, %%r14 ;"
		"movq %%r14, 48(%0) ;"
		"movq $0, %%rax ;"
		/******************************************/
		"adox %%rdx, %%rax ;"
		"adcx  %%r8, %%rax ;"
		"movq %%rax, 56(%0) ;"
		:
		: "r"(c), "r"(a), "r"(b)
		: "memory", "cc", "%rax", "%rdx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14");
}

static void mul_256x256_integer_bmi2(u64 *const c, const u64 *const a, const u64 *const b)
{
	asm volatile(
		"movq   (%1), %%rdx; "	/* A[0] */
		"mulx   (%2),  %%r8, %%r12; " /* A[0]*B[0] */
		"movq %%r8,  (%0) ;"
		"mulx  8(%2), %%r10, %%rax; " /* A[0]*B[1] */
		"addq %%r10, %%r12 ;"
		"mulx 16(%2),  %%r8, %%rbx; " /* A[0]*B[2] */
		"adcq  %%r8, %%rax ;"
		"mulx 24(%2), %%r10, %%rcx; " /* A[0]*B[3] */
		"adcq %%r10, %%rbx ;"
		/******************************************/
		"adcq    $0, %%rcx ;"

		"movq  8(%1), %%rdx; "	/* A[1] */
		"mulx   (%2),  %%r8,  %%r9; " /* A[1]*B[0] */
		"addq %%r12,  %%r8 ;"
		"movq %%r8, 8(%0) ;"
		"mulx  8(%2), %%r10, %%r11; " /* A[1]*B[1] */
		"adcq %%r10,  %%r9 ;"
		"mulx 16(%2),  %%r8, %%r13; " /* A[1]*B[2] */
		"adcq  %%r8, %%r11 ;"
		"mulx 24(%2), %%r10, %%r12; " /* A[1]*B[3] */
		"adcq %%r10, %%r13 ;"
		/******************************************/
		"adcq    $0, %%r12 ;"

		"addq  %%r9, %%rax ;"
		"adcq %%r11, %%rbx ;"
		"adcq %%r13, %%rcx ;"
		"adcq    $0, %%r12 ;"

		"movq 16(%1), %%rdx; "	/* A[2] */
		"mulx   (%2),  %%r8,  %%r9; " /* A[2]*B[0] */
		"addq %%rax,  %%r8 ;"
		"movq %%r8, 16(%0) ;"
		"mulx  8(%2), %%r10, %%r11; " /* A[2]*B[1] */
		"adcq %%r10,  %%r9 ;"
		"mulx 16(%2),  %%r8, %%r13; " /* A[2]*B[2] */
		"adcq  %%r8, %%r11 ;"
		"mulx 24(%2), %%r10, %%rax; " /* A[2]*B[3] */
		"adcq %%r10, %%r13 ;"
		/******************************************/
		"adcq    $0, %%rax ;"

		"addq  %%r9, %%rbx ;"
		"adcq %%r11, %%rcx ;"
		"adcq %%r13, %%r12 ;"
		"adcq    $0, %%rax ;"

		"movq 24(%1), %%rdx; "	/* A[3] */
		"mulx   (%2),  %%r8,  %%r9; " /* A[3]*B[0] */
		"addq %%rbx,  %%r8 ;"
		"movq %%r8, 24(%0) ;"
		"mulx  8(%2), %%r10, %%r11; " /* A[3]*B[1] */
		"adcq %%r10,  %%r9 ;"
		"mulx 16(%2),  %%r8, %%r13; " /* A[3]*B[2] */
		"adcq  %%r8, %%r11 ;"
		"mulx 24(%2), %%r10, %%rbx; " /* A[3]*B[3] */
		"adcq %%r10, %%r13 ;"
		/******************************************/
		"adcq    $0, %%rbx ;"

		"addq  %%r9, %%rcx ;"
		"movq %%rcx, 32(%0) ;"
		"adcq %%r11, %%r12 ;"
		"movq %%r12, 40(%0) ;"
		"adcq %%r13, %%rax ;"
		"movq %%rax, 48(%0) ;"
		"adcq    $0, %%rbx ;"
		"movq %%rbx, 56(%0) ;"
		:
		: "r"(c), "r"(a), "r"(b)
		: "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13");
}

static void sqr_256x256_integer_adx(u64 *const c, const u64 *const a)
{
	asm volatile(
		"movq   (%1), %%rdx        ;" /* A[0]      */
		"mulx  8(%1),  %%r8, %%r14 ;" /* A[1]*A[0] */
		"xorl %%r15d, %%r15d;"
		"mulx 16(%1),  %%r9, %%r10 ;" /* A[2]*A[0] */
		"adcx %%r14,  %%r9 ;"
		"mulx 24(%1), %%rax, %%rcx ;" /* A[3]*A[0] */
		"adcx %%rax, %%r10 ;"
		"movq 24(%1), %%rdx        ;" /* A[3]      */
		"mulx  8(%1), %%r11, %%r12 ;" /* A[1]*A[3] */
		"adcx %%rcx, %%r11 ;"
		"mulx 16(%1), %%rax, %%r13 ;" /* A[2]*A[3] */
		"adcx %%rax, %%r12 ;"
		"movq  8(%1), %%rdx        ;" /* A[1]      */
		"adcx %%r15, %%r13 ;"
		"mulx 16(%1), %%rax, %%rcx ;" /* A[2]*A[1] */
		"movq    $0, %%r14 ;"
		/******************************************/
		"adcx %%r15, %%r14 ;"

		"xorl %%r15d, %%r15d;"
		"adox %%rax, %%r10 ;"
		"adcx  %%r8,  %%r8 ;"
		"adox %%rcx, %%r11 ;"
		"adcx  %%r9,  %%r9 ;"
		"adox %%r15, %%r12 ;"
		"adcx %%r10, %%r10 ;"
		"adox %%r15, %%r13 ;"
		"adcx %%r11, %%r11 ;"
		"adox %%r15, %%r14 ;"
		"adcx %%r12, %%r12 ;"
		"adcx %%r13, %%r13 ;"
		"adcx %%r14, %%r14 ;"

		"movq   (%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ;" /* A[0]^2 */
		/*******************/
		"movq %%rax,  0(%0) ;"
		"addq %%rcx,  %%r8 ;"
		"movq  %%r8,  8(%0) ;"
		"movq  8(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ;" /* A[1]^2 */
		"adcq %%rax,  %%r9 ;"
		"movq  %%r9, 16(%0) ;"
		"adcq %%rcx, %%r10 ;"
		"movq %%r10, 24(%0) ;"
		"movq 16(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ;" /* A[2]^2 */
		"adcq %%rax, %%r11 ;"
		"movq %%r11, 32(%0) ;"
		"adcq %%rcx, %%r12 ;"
		"movq %%r12, 40(%0) ;"
		"movq 24(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ;" /* A[3]^2 */
		"adcq %%rax, %%r13 ;"
		"movq %%r13, 48(%0) ;"
		"adcq %%rcx, %%r14 ;"
		"movq %%r14, 56(%0) ;"
		:
		: "r"(c), "r"(a)
		: "memory", "cc", "%rax", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15");
}

static void sqr_256x256_integer_bmi2(u64 *const c, const u64 *const a)
{
	asm volatile(
		"movq  8(%1), %%rdx        ;" /* A[1]      */
		"mulx   (%1),  %%r8,  %%r9 ;" /* A[0]*A[1] */
		"mulx 16(%1), %%r10, %%r11 ;" /* A[2]*A[1] */
		"mulx 24(%1), %%rcx, %%r14 ;" /* A[3]*A[1] */

		"movq 16(%1), %%rdx        ;" /* A[2]      */
		"mulx 24(%1), %%r12, %%r13 ;" /* A[3]*A[2] */
		"mulx   (%1), %%rax, %%rdx ;" /* A[0]*A[2] */

		"addq %%rax,  %%r9 ;"
		"adcq %%rdx, %%r10 ;"
		"adcq %%rcx, %%r11 ;"
		"adcq %%r14, %%r12 ;"
		"adcq    $0, %%r13 ;"
		"movq    $0, %%r14 ;"
		"adcq    $0, %%r14 ;"

		"movq   (%1), %%rdx        ;" /* A[0]      */
		"mulx 24(%1), %%rax, %%rcx ;" /* A[0]*A[3] */

		"addq %%rax, %%r10 ;"
		"adcq %%rcx, %%r11 ;"
		"adcq    $0, %%r12 ;"
		"adcq    $0, %%r13 ;"
		"adcq    $0, %%r14 ;"

		"shldq $1, %%r13, %%r14 ;"
		"shldq $1, %%r12, %%r13 ;"
		"shldq $1, %%r11, %%r12 ;"
		"shldq $1, %%r10, %%r11 ;"
		"shldq $1,  %%r9, %%r10 ;"
		"shldq $1,  %%r8,  %%r9 ;"
		"shlq  $1,  %%r8        ;"

		/*******************/
		"mulx %%rdx, %%rax, %%rcx ;" /* A[0]^2 */
		/*******************/
		"movq %%rax,  0(%0) ;"
		"addq %%rcx,  %%r8 ;"
		"movq  %%r8,  8(%0) ;"
		"movq  8(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ;" /* A[1]^2 */
		"adcq %%rax,  %%r9 ;"
		"movq  %%r9, 16(%0) ;"
		"adcq %%rcx, %%r10 ;"
		"movq %%r10, 24(%0) ;"
		"movq 16(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ;" /* A[2]^2 */
		"adcq %%rax, %%r11 ;"
		"movq %%r11, 32(%0) ;"
		"adcq %%rcx, %%r12 ;"
		"movq %%r12, 40(%0) ;"
		"movq 24(%1), %%rdx ;"
		"mulx %%rdx, %%rax, %%rcx ;" /* A[3]^2 */
		"adcq %%rax, %%r13 ;"
		"movq %%r13, 48(%0) ;"
		"adcq %%rcx, %%r14 ;"
		"movq %%r14, 56(%0) ;"
		:
		: "r"(c), "r"(a)
		: "memory", "cc", "%rax", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14");
}

static void red_eltfp25519_1w_adx(u64 *const c, const u64 *const a)
{
	asm volatile(
		"movl    $38, %%edx ;"	/* 2*c = 38 = 2^256 */
		"mulx 32(%1),  %%r8, %%r10 ;" /* c*C[4] */
		"xorl %%ebx, %%ebx ;"
		"adox   (%1),  %%r8 ;"
		"mulx 40(%1),  %%r9, %%r11 ;" /* c*C[5] */
		"adcx %%r10,  %%r9 ;"
		"adox  8(%1),  %%r9 ;"
		"mulx 48(%1), %%r10, %%rax ;" /* c*C[6] */
		"adcx %%r11, %%r10 ;"
		"adox 16(%1), %%r10 ;"
		"mulx 56(%1), %%r11, %%rcx ;" /* c*C[7] */
		"adcx %%rax, %%r11 ;"
		"adox 24(%1), %%r11 ;"
		/***************************************/
		"adcx %%rbx, %%rcx ;"
		"adox  %%rbx, %%rcx ;"
		"imul %%rdx, %%rcx ;" /* c*C[4], cf=0, of=0 */
		"adcx %%rcx,  %%r8 ;"
		"adcx %%rbx,  %%r9 ;"
		"movq  %%r9,  8(%0) ;"
		"adcx %%rbx, %%r10 ;"
		"movq %%r10, 16(%0) ;"
		"adcx %%rbx, %%r11 ;"
		"movq %%r11, 24(%0) ;"
		"mov     $0, %%ecx ;"
		"cmovc %%edx, %%ecx ;"
		"addq %%rcx,  %%r8 ;"
		"movq  %%r8,   (%0) ;"
		:
		: "r"(c), "r"(a)
		: "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11");
}

static void red_eltfp25519_1w_bmi2(u64 *const c, const u64 *const a)
{
	asm volatile(
		"movl    $38, %%edx ;"	/* 2*c = 38 = 2^256 */
		"mulx 32(%1),  %%r8, %%r10 ;" /* c*C[4] */
		"mulx 40(%1),  %%r9, %%r11 ;" /* c*C[5] */
		"addq %%r10,  %%r9 ;"
		"mulx 48(%1), %%r10, %%rax ;" /* c*C[6] */
		"adcq %%r11, %%r10 ;"
		"mulx 56(%1), %%r11, %%rcx ;" /* c*C[7] */
		"adcq %%rax, %%r11 ;"
		/***************************************/
		"adcq    $0, %%rcx ;"
		"addq   (%1),  %%r8 ;"
		"adcq  8(%1),  %%r9 ;"
		"adcq 16(%1), %%r10 ;"
		"adcq 24(%1), %%r11 ;"
		"adcq     $0, %%rcx ;"
		"imul %%rdx, %%rcx ;" /* c*C[4], cf=0 */
		"addq %%rcx,  %%r8 ;"
		"adcq    $0,  %%r9 ;"
		"movq  %%r9,  8(%0) ;"
		"adcq    $0, %%r10 ;"
		"movq %%r10, 16(%0) ;"
		"adcq    $0, %%r11 ;"
		"movq %%r11, 24(%0) ;"
		"mov     $0, %%ecx ;"
		"cmovc %%edx, %%ecx ;"
		"addq %%rcx,  %%r8 ;"
		"movq  %%r8,   (%0) ;"
		:
		: "r"(c), "r"(a)
		: "memory", "cc", "%rax", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11");
}

static __always_inline void add_eltfp25519_1w_adx(u64 *const c, const u64 *const a, const u64 *const b)
{
	asm volatile(
		"mov     $38, %%eax ;"
		"xorl  %%ecx, %%ecx ;"
		"movq   (%2),  %%r8 ;"
		"adcx   (%1),  %%r8 ;"
		"movq  8(%2),  %%r9 ;"
		"adcx  8(%1),  %%r9 ;"
		"movq 16(%2), %%r10 ;"
		"adcx 16(%1), %%r10 ;"
		"movq 24(%2), %%r11 ;"
		"adcx 24(%1), %%r11 ;"
		"cmovc %%eax, %%ecx ;"
		"xorl %%eax, %%eax  ;"
		"adcx %%rcx,  %%r8  ;"
		"adcx %%rax,  %%r9  ;"
		"movq  %%r9,  8(%0) ;"
		"adcx %%rax, %%r10  ;"
		"movq %%r10, 16(%0) ;"
		"adcx %%rax, %%r11  ;"
		"movq %%r11, 24(%0) ;"
		"mov     $38, %%ecx ;"
		"cmovc %%ecx, %%eax ;"
		"addq %%rax,  %%r8  ;"
		"movq  %%r8,   (%0) ;"
		:
		: "r"(c), "r"(a), "r"(b)
		: "memory", "cc", "%rax", "%rcx", "%r8", "%r9", "%r10", "%r11");
}

static __always_inline void add_eltfp25519_1w_bmi2(u64 *const c, const u64 *const a, const u64 *const b)
{
	asm volatile(
		"mov     $38, %%eax ;"
		"movq   (%2),  %%r8 ;"
		"addq   (%1),  %%r8 ;"
		"movq  8(%2),  %%r9 ;"
		"adcq  8(%1),  %%r9 ;"
		"movq 16(%2), %%r10 ;"
		"adcq 16(%1), %%r10 ;"
		"movq 24(%2), %%r11 ;"
		"adcq 24(%1), %%r11 ;"
		"mov      $0, %%ecx ;"
		"cmovc %%eax, %%ecx ;"
		"addq %%rcx,  %%r8  ;"
		"adcq    $0,  %%r9  ;"
		"movq  %%r9,  8(%0) ;"
		"adcq    $0, %%r10  ;"
		"movq %%r10, 16(%0) ;"
		"adcq    $0, %%r11  ;"
		"movq %%r11, 24(%0) ;"
		"mov     $0, %%ecx  ;"
		"cmovc %%eax, %%ecx ;"
		"addq %%rcx,  %%r8  ;"
		"movq  %%r8,   (%0) ;"
		:
		: "r"(c), "r"(a), "r"(b)
		: "memory", "cc", "%rax", "%rcx", "%r8", "%r9", "%r10", "%r11");
}

static __always_inline void sub_eltfp25519_1w(u64 *const c, const u64 *const a, const u64 *const b)
{
	asm volatile(
		"mov     $38, %%eax ;"
		"movq   (%1),  %%r8 ;"
		"subq   (%2),  %%r8 ;"
		"movq  8(%1),  %%r9 ;"
		"sbbq  8(%2),  %%r9 ;"
		"movq 16(%1), %%r10 ;"
		"sbbq 16(%2), %%r10 ;"
		"movq 24(%1), %%r11 ;"
		"sbbq 24(%2), %%r11 ;"
		"mov      $0, %%ecx ;"
		"cmovc %%eax, %%ecx ;"
		"subq %%rcx,  %%r8  ;"
		"sbbq    $0,  %%r9  ;"
		"movq  %%r9,  8(%0) ;"
		"sbbq    $0, %%r10  ;"
		"movq %%r10, 16(%0) ;"
		"sbbq    $0, %%r11  ;"
		"movq %%r11, 24(%0) ;"
		"mov     $0, %%ecx  ;"
		"cmovc %%eax, %%ecx ;"
		"subq %%rcx,  %%r8  ;"
		"movq  %%r8,   (%0) ;"
		:
		: "r"(c), "r"(a), "r"(b)
		: "memory", "cc", "%rax", "%rcx", "%r8", "%r9", "%r10", "%r11");
}

/* Multiplication by a24 = (A+2)/4 = (486662+2)/4 = 121666 */
static __always_inline void mul_a24_eltfp25519_1w(u64 *const c, const u64 *const a)
{
	const u64 a24 = 121666;
	asm volatile(
		"movq     %2, %%rdx ;"
		"mulx   (%1),  %%r8, %%r10 ;"
		"mulx  8(%1),  %%r9, %%r11 ;"
		"addq %%r10,  %%r9 ;"
		"mulx 16(%1), %%r10, %%rax ;"
		"adcq %%r11, %%r10 ;"
		"mulx 24(%1), %%r11, %%rcx ;"
		"adcq %%rax, %%r11 ;"
		/**************************/
		"adcq    $0, %%rcx ;"
		"movl   $38, %%edx ;" /* 2*c = 38 = 2^256 mod 2^255-19*/
		"imul %%rdx, %%rcx ;"
		"addq %%rcx,  %%r8 ;"
		"adcq    $0,  %%r9 ;"
		"movq  %%r9,  8(%0) ;"
		"adcq    $0, %%r10 ;"
		"movq %%r10, 16(%0) ;"
		"adcq    $0, %%r11 ;"
		"movq %%r11, 24(%0) ;"
		"mov     $0, %%ecx ;"
		"cmovc %%edx, %%ecx ;"
		"addq %%rcx,  %%r8 ;"
		"movq  %%r8,   (%0) ;"
		:
		: "r"(c), "r"(a), "r"(a24)
		: "memory", "cc", "%rax", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11");
}

static void inv_eltfp25519_1w_adx(u64 *const c, const u64 *const a)
{
	struct {
		eltfp25519_1w_buffer buffer;
		eltfp25519_1w x0, x1, x2;
	} __attribute((aligned(32))) m;
	u64 *T[4];

	T[0] = m.x0;
	T[1] = c; /* x^(-1) */
	T[2] = m.x1;
	T[3] = m.x2;

	copy_eltfp25519_1w(T[1], a);
	sqrn_eltfp25519_1w_adx(T[1], 1);
	copy_eltfp25519_1w(T[2], T[1]);
	sqrn_eltfp25519_1w_adx(T[2], 2);
	mul_eltfp25519_1w_adx(T[0], a, T[2]);
	mul_eltfp25519_1w_adx(T[1], T[1], T[0]);
	copy_eltfp25519_1w(T[2], T[1]);
	sqrn_eltfp25519_1w_adx(T[2], 1);
	mul_eltfp25519_1w_adx(T[0], T[0], T[2]);
	copy_eltfp25519_1w(T[2], T[0]);
	sqrn_eltfp25519_1w_adx(T[2], 5);
	mul_eltfp25519_1w_adx(T[0], T[0], T[2]);
	copy_eltfp25519_1w(T[2], T[0]);
	sqrn_eltfp25519_1w_adx(T[2], 10);
	mul_eltfp25519_1w_adx(T[2], T[2], T[0]);
	copy_eltfp25519_1w(T[3], T[2]);
	sqrn_eltfp25519_1w_adx(T[3], 20);
	mul_eltfp25519_1w_adx(T[3], T[3], T[2]);
	sqrn_eltfp25519_1w_adx(T[3], 10);
	mul_eltfp25519_1w_adx(T[3], T[3], T[0]);
	copy_eltfp25519_1w(T[0], T[3]);
	sqrn_eltfp25519_1w_adx(T[0], 50);
	mul_eltfp25519_1w_adx(T[0], T[0], T[3]);
	copy_eltfp25519_1w(T[2], T[0]);
	sqrn_eltfp25519_1w_adx(T[2], 100);
	mul_eltfp25519_1w_adx(T[2], T[2], T[0]);
	sqrn_eltfp25519_1w_adx(T[2], 50);
	mul_eltfp25519_1w_adx(T[2], T[2], T[3]);
	sqrn_eltfp25519_1w_adx(T[2], 5);
	mul_eltfp25519_1w_adx(T[1], T[1], T[2]);
}

static void inv_eltfp25519_1w_bmi2(u64 *const c, const u64 *const a)
{
	struct {
		eltfp25519_1w_buffer buffer;
		eltfp25519_1w x0, x1, x2;
	} __attribute((aligned(32))) m;
	u64 *T[5];

	T[0] = m.x0;
	T[1] = c; /* x^(-1) */
	T[2] = m.x1;
	T[3] = m.x2;

	copy_eltfp25519_1w(T[1], a);
	sqrn_eltfp25519_1w_bmi2(T[1], 1);
	copy_eltfp25519_1w(T[2], T[1]);
	sqrn_eltfp25519_1w_bmi2(T[2], 2);
	mul_eltfp25519_1w_bmi2(T[0], a, T[2]);
	mul_eltfp25519_1w_bmi2(T[1], T[1], T[0]);
	copy_eltfp25519_1w(T[2], T[1]);
	sqrn_eltfp25519_1w_bmi2(T[2], 1);
	mul_eltfp25519_1w_bmi2(T[0], T[0], T[2]);
	copy_eltfp25519_1w(T[2], T[0]);
	sqrn_eltfp25519_1w_bmi2(T[2], 5);
	mul_eltfp25519_1w_bmi2(T[0], T[0], T[2]);
	copy_eltfp25519_1w(T[2], T[0]);
	sqrn_eltfp25519_1w_bmi2(T[2], 10);
	mul_eltfp25519_1w_bmi2(T[2], T[2], T[0]);
	copy_eltfp25519_1w(T[3], T[2]);
	sqrn_eltfp25519_1w_bmi2(T[3], 20);
	mul_eltfp25519_1w_bmi2(T[3], T[3], T[2]);
	sqrn_eltfp25519_1w_bmi2(T[3], 10);
	mul_eltfp25519_1w_bmi2(T[3], T[3], T[0]);
	copy_eltfp25519_1w(T[0], T[3]);
	sqrn_eltfp25519_1w_bmi2(T[0], 50);
	mul_eltfp25519_1w_bmi2(T[0], T[0], T[3]);
	copy_eltfp25519_1w(T[2], T[0]);
	sqrn_eltfp25519_1w_bmi2(T[2], 100);
	mul_eltfp25519_1w_bmi2(T[2], T[2], T[0]);
	sqrn_eltfp25519_1w_bmi2(T[2], 50);
	mul_eltfp25519_1w_bmi2(T[2], T[2], T[3]);
	sqrn_eltfp25519_1w_bmi2(T[2], 5);
	mul_eltfp25519_1w_bmi2(T[1], T[1], T[2]);
}

/* Given c, a 256-bit number, fred_eltfp25519_1w updates c
 * with a number such that 0 <= C < 2**255-19.
 */
static __always_inline void fred_eltfp25519_1w(u64 *const c)
{
	u64 tmp0, tmp1;
	asm volatile(
		"movl   $19,   %k5 ;"
		"movl   $38,   %k4 ;"

		"btrq   $63,    %3 ;" /* Put bit 255 in carry flag and clear */
		"cmovncl %k5,   %k4 ;" /* c[255] ? 38 : 19 */

		/* Add either 19 or 38 to c */
		"addq    %4,   %0 ;"
		"adcq    $0,   %1 ;"
		"adcq    $0,   %2 ;"
		"adcq    $0,   %3 ;"

		/* Test for bit 255 again; only triggered on overflow modulo 2^255-19 */
		"movl    $0,  %k4 ;"
		"cmovnsl %k5,  %k4 ;" /* c[255] ? 0 : 19 */
		"btrq   $63,   %3 ;" /* Clear bit 255 */

		/* Subtract 19 if necessary */
		"subq    %4,   %0 ;"
		"sbbq    $0,   %1 ;"
		"sbbq    $0,   %2 ;"
		"sbbq    $0,   %3 ;"

		: "+r"(c[0]), "+r"(c[1]), "+r"(c[2]), "+r"(c[3]), "=r"(tmp0), "=r"(tmp1)
		:
		: "memory", "cc");
}

static __always_inline void cselect(u8 bit, u64 *const px, const u64 *const py)
{
	asm volatile(
		"test %4, %4 ;"
		"cmovnzq %5, %0 ;"
		"cmovnzq %6, %1 ;"
		"cmovnzq %7, %2 ;"
		"cmovnzq %8, %3 ;"
		: "+r"(px[0]), "+r"(px[1]), "+r"(px[2]), "+r"(px[3])
		: "r"(bit), "rm"(py[0]), "rm"(py[1]), "rm"(py[2]), "rm"(py[3])
		: "cc"
	);
}

bool curve25519_precomp_adx(u8 shared[CURVE25519_POINT_SIZE], const u8 private_key[CURVE25519_POINT_SIZE], const u8 session_key[CURVE25519_POINT_SIZE])
{
	struct {
		u64 buffer[4 * NUM_WORDS_ELTFP25519];
		u64 coordinates[4 * NUM_WORDS_ELTFP25519];
		u64 workspace[6 * NUM_WORDS_ELTFP25519];
		u8 session[CURVE25519_POINT_SIZE];
		u8 private[CURVE25519_POINT_SIZE];
	} __attribute((aligned(32))) m;

	int i = 0, j = 0;
	u64 prev = 0;
	u64 *const X1 = (u64 *)m.session;
	u64 *const key = (u64 *)m.private;
	u64 *const Px = m.coordinates + 0;
	u64 *const Pz = m.coordinates + 4;
	u64 *const Qx = m.coordinates + 8;
	u64 *const Qz = m.coordinates + 12;
	u64 *const X2 = Qx;
	u64 *const Z2 = Qz;
	u64 *const X3 = Px;
	u64 *const Z3 = Pz;
	u64 *const X2Z2 = Qx;
	u64 *const X3Z3 = Px;

	u64 *const A = m.workspace + 0;
	u64 *const B = m.workspace + 4;
	u64 *const D = m.workspace + 8;
	u64 *const C = m.workspace + 12;
	u64 *const DA = m.workspace + 16;
	u64 *const CB = m.workspace + 20;
	u64 *const AB = A;
	u64 *const DC = D;
	u64 *const DACB = DA;

	memcpy(m.private, private_key, sizeof(m.private));
	memcpy(m.session, session_key, sizeof(m.session));

	normalize_secret(m.private);

	/* As in the draft:
	 * When receiving such an array, implementations of curve25519
	 * MUST mask the most-significant bit in the final byte. This
	 * is done to preserve compatibility with point formats which
	 * reserve the sign bit for use in other protocols and to
	 * increase resistance to implementation fingerprinting
	 */
	m.session[CURVE25519_POINT_SIZE - 1] &= (1 << (255 % 8)) - 1;

	copy_eltfp25519_1w(Px, X1);
	setzero_eltfp25519_1w(Pz);
	setzero_eltfp25519_1w(Qx);
	setzero_eltfp25519_1w(Qz);

	Pz[0] = 1;
	Qx[0] = 1;

	/* main-loop */
	prev = 0;
	j = 62;
	for (i = 3; i >= 0; --i) {
		while (j >= 0) {
			u64 bit = (key[i] >> j) & 0x1;
			u64 swap = bit ^ prev;
			prev = bit;

			add_eltfp25519_1w_adx(A, X2, Z2);	/* A = (X2+Z2) */
			sub_eltfp25519_1w(B, X2, Z2);		/* B = (X2-Z2) */
			add_eltfp25519_1w_adx(C, X3, Z3);	/* C = (X3+Z3) */
			sub_eltfp25519_1w(D, X3, Z3);		/* D = (X3-Z3) */
			mul_eltfp25519_2w_adx(DACB, AB, DC);	/* [DA|CB] = [A|B]*[D|C] */

			cselect(swap, A, C);
			cselect(swap, B, D);

			sqr_eltfp25519_2w_adx(AB);		/* [AA|BB] = [A^2|B^2] */
			add_eltfp25519_1w_adx(X3, DA, CB);	/* X3 = (DA+CB) */
			sub_eltfp25519_1w(Z3, DA, CB);		/* Z3 = (DA-CB) */
			sqr_eltfp25519_2w_adx(X3Z3);		/* [X3|Z3] = [(DA+CB)|(DA+CB)]^2 */

			copy_eltfp25519_1w(X2, B);		/* X2 = B^2 */
			sub_eltfp25519_1w(Z2, A, B);		/* Z2 = E = AA-BB */

			mul_a24_eltfp25519_1w(B, Z2);		/* B = a24*E */
			add_eltfp25519_1w_adx(B, B, X2);	/* B = a24*E+B */
			mul_eltfp25519_2w_adx(X2Z2, X2Z2, AB);	/* [X2|Z2] = [B|E]*[A|a24*E+B] */
			mul_eltfp25519_1w_adx(Z3, Z3, X1);	/* Z3 = Z3*X1 */
			--j;
		}
		j = 63;
	}

	inv_eltfp25519_1w_adx(A, Qz);
	mul_eltfp25519_1w_adx((u64 *)shared, Qx, A);
	fred_eltfp25519_1w((u64 *)shared);

	return true;
}

bool curve25519_precomp_bmi2(u8 shared[CURVE25519_POINT_SIZE], const u8 private_key[CURVE25519_POINT_SIZE], const u8 session_key[CURVE25519_POINT_SIZE])
{
	struct {
		u64 buffer[4 * NUM_WORDS_ELTFP25519];
		u64 coordinates[4 * NUM_WORDS_ELTFP25519];
		u64 workspace[6 * NUM_WORDS_ELTFP25519];
		u8 session[CURVE25519_POINT_SIZE];
		u8 private[CURVE25519_POINT_SIZE];
	} __attribute((aligned(32))) m;

	int i = 0, j = 0;
	u64 prev = 0;
	u64 *const X1 = (u64 *)m.session;
	u64 *const key = (u64 *)m.private;
	u64 *const Px = m.coordinates + 0;
	u64 *const Pz = m.coordinates + 4;
	u64 *const Qx = m.coordinates + 8;
	u64 *const Qz = m.coordinates + 12;
	u64 *const X2 = Qx;
	u64 *const Z2 = Qz;
	u64 *const X3 = Px;
	u64 *const Z3 = Pz;
	u64 *const X2Z2 = Qx;
	u64 *const X3Z3 = Px;

	u64 *const A = m.workspace + 0;
	u64 *const B = m.workspace + 4;
	u64 *const D = m.workspace + 8;
	u64 *const C = m.workspace + 12;
	u64 *const DA = m.workspace + 16;
	u64 *const CB = m.workspace + 20;
	u64 *const AB = A;
	u64 *const DC = D;
	u64 *const DACB = DA;

	memcpy(m.private, private_key, sizeof(m.private));
	memcpy(m.session, session_key, sizeof(m.session));

	normalize_secret(m.private);

	/* As in the draft:
	 * When receiving such an array, implementations of curve25519
	 * MUST mask the most-significant bit in the final byte. This
	 * is done to preserve compatibility with point formats which
	 * reserve the sign bit for use in other protocols and to
	 * increase resistance to implementation fingerprinting
	 */
	m.session[CURVE25519_POINT_SIZE - 1] &= (1 << (255 % 8)) - 1;

	copy_eltfp25519_1w(Px, X1);
	setzero_eltfp25519_1w(Pz);
	setzero_eltfp25519_1w(Qx);
	setzero_eltfp25519_1w(Qz);

	Pz[0] = 1;
	Qx[0] = 1;

	/* main-loop */
	prev = 0;
	j = 62;
	for (i = 3; i >= 0; --i) {
		while (j >= 0) {
			u64 bit = (key[i] >> j) & 0x1;
			u64 swap = bit ^ prev;
			prev = bit;

			add_eltfp25519_1w_bmi2(A, X2, Z2);	/* A = (X2+Z2) */
			sub_eltfp25519_1w(B, X2, Z2);		/* B = (X2-Z2) */
			add_eltfp25519_1w_bmi2(C, X3, Z3);	/* C = (X3+Z3) */
			sub_eltfp25519_1w(D, X3, Z3);		/* D = (X3-Z3) */
			mul_eltfp25519_2w_bmi2(DACB, AB, DC);	/* [DA|CB] = [A|B]*[D|C] */

			cselect(swap, A, C);
			cselect(swap, B, D);

			sqr_eltfp25519_2w_bmi2(AB);		/* [AA|BB] = [A^2|B^2] */
			add_eltfp25519_1w_bmi2(X3, DA, CB);	/* X3 = (DA+CB) */
			sub_eltfp25519_1w(Z3, DA, CB);		/* Z3 = (DA-CB) */
			sqr_eltfp25519_2w_bmi2(X3Z3);		/* [X3|Z3] = [(DA+CB)|(DA+CB)]^2 */

			copy_eltfp25519_1w(X2, B);		/* X2 = B^2 */
			sub_eltfp25519_1w(Z2, A, B);		/* Z2 = E = AA-BB */

			mul_a24_eltfp25519_1w(B, Z2);		/* B = a24*E */
			add_eltfp25519_1w_bmi2(B, B, X2);	/* B = a24*E+B */
			mul_eltfp25519_2w_bmi2(X2Z2, X2Z2, AB);	/* [X2|Z2] = [B|E]*[A|a24*E+B] */
			mul_eltfp25519_1w_bmi2(Z3, Z3, X1);	/* Z3 = Z3*X1 */
			--j;
		}
		j = 63;
	}

	inv_eltfp25519_1w_bmi2(A, Qz);
	mul_eltfp25519_1w_bmi2((u64 *)shared, Qx, A);
	fred_eltfp25519_1w((u64 *)shared);

	return true;
}
