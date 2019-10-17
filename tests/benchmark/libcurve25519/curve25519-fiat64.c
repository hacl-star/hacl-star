/* SPDX-License-Identifier: GPL-2.0
 *
 * Copyright (C) 2015-2016 The fiat-crypto Authors.
 * Copyright (C) 2018 Jason A. Donenfeld <Jason@zx2c4.com>. All Rights Reserved.
 *
 * This is a machine-generated formally verified implementation of curve25519 DH from:
 * https://github.com/mit-plv/fiat-crypto
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

/* fe means field element. Here the field is \Z/(2^255-19). An element t,
 * entries t[0]...t[4], represents the integer t[0]+2^51 t[1]+2^102 t[2]+2^153
 * t[3]+2^204 t[4].
 * fe limbs are bounded by 1.125*2^51.
 * Multiplication and carrying produce fe from fe_loose.
 */
typedef struct fe { u64 v[5]; } fe;

/* fe_loose limbs are bounded by 3.375*2^51.
 * Addition and subtraction produce fe_loose from (fe, fe).
 */
typedef struct fe_loose { u64 v[5]; } fe_loose;

static __always_inline void fe_frombytes_impl(u64 h[5], const u8 *s)
{
  // Ignores top bit of s.
  u64 a0 = load64_le(s);
  u64 a1 = load64_le(s+8);
  u64 a2 = load64_le(s+16);
  u64 a3 = load64_le(s+24);

	// Use 51 bits, 64-51 = 13 left.
	h[0] = a0 & ((1ULL << 51) - 1);
	// (64-51) + 38 = 13 + 38 = 51
	h[1] = (a0 >> 51) | ((a1 & ((1ULL << 38) - 1)) << 13);
	// (64-38) + 25 = 26 + 25 = 51
	h[2] = (a1 >> 38) | ((a2 & ((1ULL << 25) - 1)) << 26);
	// (64-25) + 12 = 39 + 12 = 51
	h[3] = (a2 >> 25) | ((a3 & ((1ULL << 12) - 1)) << 39);
	// (64-12) = 52, ignore top bit
	h[4] = (a3 >> 12) & ((1ULL << 51) - 1);
}

static __always_inline void fe_frombytes(fe *h, const u8 *s)
{
	fe_frombytes_impl(h->v, s);
}

static __always_inline u8 /*bool*/ addcarryx_u51(u8 /*bool*/ c, u64 a, u64 b, u64 *low)
{
	/* This function extracts 51 bits of result and 1 bit of carry (52 total), so
	 *a 64-bit intermediate is sufficient.
	 */
	u64 x = a + b + c;
	*low = x & ((1ULL << 51) - 1);
	return (x >> 51) & 1;
}

static __always_inline u8 /*bool*/ subborrow_u51(u8 /*bool*/ c, u64 a, u64 b, u64 *low)
{
	/* This function extracts 51 bits of result and 1 bit of borrow (52 total), so
	 * a 64-bit intermediate is sufficient.
	 */
	u64 x = a - b - c;
	*low = x & ((1ULL << 51) - 1);
	return x >> 63;
}

static __always_inline u64 cmovznz64(u64 t, u64 z, u64 nz)
{
	/* all set if nonzero, 0 if 0 */
	t = -!!t;
	return (t&nz) | ((~t)&z);
}

static __always_inline void fe_freeze(u64 out[5], const u64 in1[5])
{
	{ const u64 x7 = in1[4];
	{ const u64 x8 = in1[3];
	{ const u64 x6 = in1[2];
	{ const u64 x4 = in1[1];
	{ const u64 x2 = in1[0];
	{ u64 x10; u8/*bool*/ x11 = subborrow_u51(0x0, x2, 0x7ffffffffffed, &x10);
	{ u64 x13; u8/*bool*/ x14 = subborrow_u51(x11, x4, 0x7ffffffffffff, &x13);
	{ u64 x16; u8/*bool*/ x17 = subborrow_u51(x14, x6, 0x7ffffffffffff, &x16);
	{ u64 x19; u8/*bool*/ x20 = subborrow_u51(x17, x8, 0x7ffffffffffff, &x19);
	{ u64 x22; u8/*bool*/ x23 = subborrow_u51(x20, x7, 0x7ffffffffffff, &x22);
	{ u64 x24 = cmovznz64(x23, 0x0, 0xffffffffffffffffL);
	{ u64 x25 = (x24 & 0x7ffffffffffed);
	{ u64 x27; u8/*bool*/ x28 = addcarryx_u51(0x0, x10, x25, &x27);
	{ u64 x29 = (x24 & 0x7ffffffffffff);
	{ u64 x31; u8/*bool*/ x32 = addcarryx_u51(x28, x13, x29, &x31);
	{ u64 x33 = (x24 & 0x7ffffffffffff);
	{ u64 x35; u8/*bool*/ x36 = addcarryx_u51(x32, x16, x33, &x35);
	{ u64 x37 = (x24 & 0x7ffffffffffff);
	{ u64 x39; u8/*bool*/ x40 = addcarryx_u51(x36, x19, x37, &x39);
	{ u64 x41 = (x24 & 0x7ffffffffffff);
	{ u64 x43; addcarryx_u51(x40, x22, x41, &x43);
	out[0] = x27;
	out[1] = x31;
	out[2] = x35;
	out[3] = x39;
	out[4] = x43;
	}}}}}}}}}}}}}}}}}}}}}
}

static __always_inline void fe_tobytes(u8 s[32], const fe *f)
{
	u64 h[5];
	fe_freeze(h, f->v);

	s[0] = h[0] >> 0;
	s[1] = h[0] >> 8;
	s[2] = h[0] >> 16;
	s[3] = h[0] >> 24;
	s[4] = h[0] >> 32;
	s[5] = h[0] >> 40;
	s[6] = (h[0] >> 48) | (h[1] << 3);
	s[7] = h[1] >> 5;
	s[8] = h[1] >> 13;
	s[9] = h[1] >> 21;
	s[10] = h[1] >> 29;
	s[11] = h[1] >> 37;
	s[12] = (h[1] >> 45) | (h[2] << 6);
	s[13] = h[2] >> 2;
	s[14] = h[2] >> 10;
	s[15] = h[2] >> 18;
	s[16] = h[2] >> 26;
	s[17] = h[2] >> 34;
	s[18] = h[2] >> 42;
	s[19] = (h[2] >> 50) | (h[3] << 1);
	s[20] = h[3] >> 7;
	s[21] = h[3] >> 15;
	s[22] = h[3] >> 23;
	s[23] = h[3] >> 31;
	s[24] = h[3] >> 39;
	s[25] = (h[3] >> 47) | (h[4] << 4);
	s[26] = h[4] >> 4;
	s[27] = h[4] >> 12;
	s[28] = h[4] >> 20;
	s[29] = h[4] >> 28;
	s[30] = h[4] >> 36;
	s[31] = h[4] >> 44;
}

/* h = f */
static __always_inline void fe_copy(fe *h, const fe *f)
{
	memmove(h, f, sizeof(fe));
}

static __always_inline void fe_copy_lt(fe_loose *h, const fe *f)
{
	memmove(h, f, sizeof(fe));
}

/* h = 0 */
static __always_inline void fe_0(fe *h)
{
	memset(h, 0, sizeof(fe));
}

/* h = 1 */
static __always_inline void fe_1(fe *h)
{
	memset(h, 0, sizeof(fe));
	h->v[0] = 1;
}

static __always_inline void fe_add_impl(u64 out[5], const u64 in1[5], const u64 in2[5])
{
	{ const u64 x10 = in1[4];
	{ const u64 x11 = in1[3];
	{ const u64 x9 = in1[2];
	{ const u64 x7 = in1[1];
	{ const u64 x5 = in1[0];
	{ const u64 x18 = in2[4];
	{ const u64 x19 = in2[3];
	{ const u64 x17 = in2[2];
	{ const u64 x15 = in2[1];
	{ const u64 x13 = in2[0];
	out[0] = (x5 + x13);
	out[1] = (x7 + x15);
	out[2] = (x9 + x17);
	out[3] = (x11 + x19);
	out[4] = (x10 + x18);
	}}}}}}}}}}
}

/* h = f + g
 * Can overlap h with f or g.
 */
static __always_inline void fe_add(fe_loose *h, const fe *f, const fe *g)
{
	fe_add_impl(h->v, f->v, g->v);
}

static __always_inline void fe_sub_impl(u64 out[5], const u64 in1[5], const u64 in2[5])
{
	{ const u64 x10 = in1[4];
	{ const u64 x11 = in1[3];
	{ const u64 x9 = in1[2];
	{ const u64 x7 = in1[1];
	{ const u64 x5 = in1[0];
	{ const u64 x18 = in2[4];
	{ const u64 x19 = in2[3];
	{ const u64 x17 = in2[2];
	{ const u64 x15 = in2[1];
	{ const u64 x13 = in2[0];
	out[0] = ((0xfffffffffffda + x5) - x13);
	out[1] = ((0xffffffffffffe + x7) - x15);
	out[2] = ((0xffffffffffffe + x9) - x17);
	out[3] = ((0xffffffffffffe + x11) - x19);
	out[4] = ((0xffffffffffffe + x10) - x18);
	}}}}}}}}}}
}

/* h = f - g
 * Can overlap h with f or g.
 */
static __always_inline void fe_sub(fe_loose *h, const fe *f, const fe *g)
{
	fe_sub_impl(h->v, f->v, g->v);
}

static __always_inline void fe_mul_impl(u64 out[5], const u64 in1[5], const u64 in2[5])
{
	{ const u64 x10 = in1[4];
	{ const u64 x11 = in1[3];
	{ const u64 x9 = in1[2];
	{ const u64 x7 = in1[1];
	{ const u64 x5 = in1[0];
	{ const u64 x18 = in2[4];
	{ const u64 x19 = in2[3];
	{ const u64 x17 = in2[2];
	{ const u64 x15 = in2[1];
	{ const u64 x13 = in2[0];
	{ u128 x20 = ((u128)x5 * x13);
	{ u128 x21 = (((u128)x5 * x15) + ((u128)x7 * x13));
	{ u128 x22 = ((((u128)x5 * x17) + ((u128)x9 * x13)) + ((u128)x7 * x15));
	{ u128 x23 = (((((u128)x5 * x19) + ((u128)x11 * x13)) + ((u128)x7 * x17)) + ((u128)x9 * x15));
	{ u128 x24 = ((((((u128)x5 * x18) + ((u128)x10 * x13)) + ((u128)x11 * x15)) + ((u128)x7 * x19)) + ((u128)x9 * x17));
	{ u64 x25 = (x10 * 0x13);
	{ u64 x26 = (x7 * 0x13);
	{ u64 x27 = (x9 * 0x13);
	{ u64 x28 = (x11 * 0x13);
	{ u128 x29 = ((((x20 + ((u128)x25 * x15)) + ((u128)x26 * x18)) + ((u128)x27 * x19)) + ((u128)x28 * x17));
	{ u128 x30 = (((x21 + ((u128)x25 * x17)) + ((u128)x27 * x18)) + ((u128)x28 * x19));
	{ u128 x31 = ((x22 + ((u128)x25 * x19)) + ((u128)x28 * x18));
	{ u128 x32 = (x23 + ((u128)x25 * x18));
	{ u64 x33 = (u64) (x29 >> 0x33);
	{ u64 x34 = ((u64)x29 & 0x7ffffffffffff);
	{ u128 x35 = (x33 + x30);
	{ u64 x36 = (u64) (x35 >> 0x33);
	{ u64 x37 = ((u64)x35 & 0x7ffffffffffff);
	{ u128 x38 = (x36 + x31);
	{ u64 x39 = (u64) (x38 >> 0x33);
	{ u64 x40 = ((u64)x38 & 0x7ffffffffffff);
	{ u128 x41 = (x39 + x32);
	{ u64 x42 = (u64) (x41 >> 0x33);
	{ u64 x43 = ((u64)x41 & 0x7ffffffffffff);
	{ u128 x44 = (x42 + x24);
	{ u64 x45 = (u64) (x44 >> 0x33);
	{ u64 x46 = ((u64)x44 & 0x7ffffffffffff);
	{ u64 x47 = (x34 + (0x13 * x45));
	{ u64 x48 = (x47 >> 0x33);
	{ u64 x49 = (x47 & 0x7ffffffffffff);
	{ u64 x50 = (x48 + x37);
	{ u64 x51 = (x50 >> 0x33);
	{ u64 x52 = (x50 & 0x7ffffffffffff);
	out[0] = x49;
	out[1] = x52;
	out[2] = (x51 + x40);
	out[3] = x43;
	out[4] = x46;
	}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}

static __always_inline void fe_mul_ttt(fe *h, const fe *f, const fe *g)
{
	fe_mul_impl(h->v, f->v, g->v);
}

static __always_inline void fe_mul_tlt(fe *h, const fe_loose *f, const fe *g)
{
	fe_mul_impl(h->v, f->v, g->v);
}

static __always_inline void fe_mul_tll(fe *h, const fe_loose *f, const fe_loose *g)
{
	fe_mul_impl(h->v, f->v, g->v);
}


static __always_inline void fe_sqr_impl(u64 out[5], const u64 in1[5])
{
	{ const u64 x7 = in1[4];
	{ const u64 x8 = in1[3];
	{ const u64 x6 = in1[2];
	{ const u64 x4 = in1[1];
	{ const u64 x2 = in1[0];
	{ u64 x9 = (x2 * 0x2);
	{ u64 x10 = (x4 * 0x2);
	{ u64 x11 = ((x6 * 0x2) * 0x13);
	{ u64 x12 = (x7 * 0x13);
	{ u64 x13 = (x12 * 0x2);
	{ u128 x14 = ((((u128)x2 * x2) + ((u128)x13 * x4)) + ((u128)x11 * x8));
	{ u128 x15 = ((((u128)x9 * x4) + ((u128)x13 * x6)) + ((u128)x8 * (x8 * 0x13)));
	{ u128 x16 = ((((u128)x9 * x6) + ((u128)x4 * x4)) + ((u128)x13 * x8));
	{ u128 x17 = ((((u128)x9 * x8) + ((u128)x10 * x6)) + ((u128)x7 * x12));
	{ u128 x18 = ((((u128)x9 * x7) + ((u128)x10 * x8)) + ((u128)x6 * x6));
	{ u64 x19 = (u64) (x14 >> 0x33);
	{ u64 x20 = ((u64)x14 & 0x7ffffffffffff);
	{ u128 x21 = (x19 + x15);
	{ u64 x22 = (u64) (x21 >> 0x33);
	{ u64 x23 = ((u64)x21 & 0x7ffffffffffff);
	{ u128 x24 = (x22 + x16);
	{ u64 x25 = (u64) (x24 >> 0x33);
	{ u64 x26 = ((u64)x24 & 0x7ffffffffffff);
	{ u128 x27 = (x25 + x17);
	{ u64 x28 = (u64) (x27 >> 0x33);
	{ u64 x29 = ((u64)x27 & 0x7ffffffffffff);
	{ u128 x30 = (x28 + x18);
	{ u64 x31 = (u64) (x30 >> 0x33);
	{ u64 x32 = ((u64)x30 & 0x7ffffffffffff);
	{ u64 x33 = (x20 + (0x13 * x31));
	{ u64 x34 = (x33 >> 0x33);
	{ u64 x35 = (x33 & 0x7ffffffffffff);
	{ u64 x36 = (x34 + x23);
	{ u64 x37 = (x36 >> 0x33);
	{ u64 x38 = (x36 & 0x7ffffffffffff);
	out[0] = x35;
	out[1] = x38;
	out[2] = (x37 + x26);
	out[3] = x29;
	out[4] = x32;
	}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}

static __always_inline void fe_sq_tl(fe *h, const fe_loose *f)
{
	fe_sqr_impl(h->v, f->v);
}

static __always_inline void fe_sq_tt(fe *h, const fe *f)
{
	fe_sqr_impl(h->v, f->v);
}

static __always_inline void fe_loose_invert(fe *out, const fe_loose *z)
{
	fe t0;
	fe t1;
	fe t2;
	fe t3;
	int i;

	fe_sq_tl(&t0, z);
	fe_sq_tt(&t1, &t0);
	for (i = 1; i < 2; ++i)
		fe_sq_tt(&t1, &t1);
	fe_mul_tlt(&t1, z, &t1);
	fe_mul_ttt(&t0, &t0, &t1);
	fe_sq_tt(&t2, &t0);
	fe_mul_ttt(&t1, &t1, &t2);
	fe_sq_tt(&t2, &t1);
	for (i = 1; i < 5; ++i)
		fe_sq_tt(&t2, &t2);
	fe_mul_ttt(&t1, &t2, &t1);
	fe_sq_tt(&t2, &t1);
	for (i = 1; i < 10; ++i)
		fe_sq_tt(&t2, &t2);
	fe_mul_ttt(&t2, &t2, &t1);
	fe_sq_tt(&t3, &t2);
	for (i = 1; i < 20; ++i)
		fe_sq_tt(&t3, &t3);
	fe_mul_ttt(&t2, &t3, &t2);
	fe_sq_tt(&t2, &t2);
	for (i = 1; i < 10; ++i)
		fe_sq_tt(&t2, &t2);
	fe_mul_ttt(&t1, &t2, &t1);
	fe_sq_tt(&t2, &t1);
	for (i = 1; i < 50; ++i)
		fe_sq_tt(&t2, &t2);
	fe_mul_ttt(&t2, &t2, &t1);
	fe_sq_tt(&t3, &t2);
	for (i = 1; i < 100; ++i)
		fe_sq_tt(&t3, &t3);
	fe_mul_ttt(&t2, &t3, &t2);
	fe_sq_tt(&t2, &t2);
	for (i = 1; i < 50; ++i)
		fe_sq_tt(&t2, &t2);
	fe_mul_ttt(&t1, &t2, &t1);
	fe_sq_tt(&t1, &t1);
	for (i = 1; i < 5; ++i)
		fe_sq_tt(&t1, &t1);
	fe_mul_ttt(out, &t1, &t0);
}

static __always_inline void fe_invert(fe *out, const fe *z)
{
	fe_loose l;
	fe_copy_lt(&l, z);
	fe_loose_invert(out, &l);
}

/* Replace (f,g) with (g,f) if b == 1;
 * replace (f,g) with (f,g) if b == 0.
 *
 * Preconditions: b in {0,1}
 */
static __always_inline void fe_cswap(fe *f, fe *g, u64 b)
{
	unsigned i;
	b = 0-b;
	for (i = 0; i < 5; i++) {
		u64 x = f->v[i] ^ g->v[i];
		x &= b;
		f->v[i] ^= x;
		g->v[i] ^= x;
	}
}

/* NOTE: based on fiat-crypto fe_mul, edited for in2=121666, 0, 0.*/
static __always_inline void fe_mul_121666_impl(u64 out[5], const u64 in1[5])
{
	{ const u64 x10 = in1[4];
	{ const u64 x11 = in1[3];
	{ const u64 x9 = in1[2];
	{ const u64 x7 = in1[1];
	{ const u64 x5 = in1[0];
	{ const u64 x18 = 0;
	{ const u64 x19 = 0;
	{ const u64 x17 = 0;
	{ const u64 x15 = 0;
	{ const u64 x13 = 121666;
	{ u128 x20 = ((u128)x5 * x13);
	{ u128 x21 = (((u128)x5 * x15) + ((u128)x7 * x13));
	{ u128 x22 = ((((u128)x5 * x17) + ((u128)x9 * x13)) + ((u128)x7 * x15));
	{ u128 x23 = (((((u128)x5 * x19) + ((u128)x11 * x13)) + ((u128)x7 * x17)) + ((u128)x9 * x15));
	{ u128 x24 = ((((((u128)x5 * x18) + ((u128)x10 * x13)) + ((u128)x11 * x15)) + ((u128)x7 * x19)) + ((u128)x9 * x17));
	{ u64 x25 = (x10 * 0x13);
	{ u64 x26 = (x7 * 0x13);
	{ u64 x27 = (x9 * 0x13);
	{ u64 x28 = (x11 * 0x13);
	{ u128 x29 = ((((x20 + ((u128)x25 * x15)) + ((u128)x26 * x18)) + ((u128)x27 * x19)) + ((u128)x28 * x17));
	{ u128 x30 = (((x21 + ((u128)x25 * x17)) + ((u128)x27 * x18)) + ((u128)x28 * x19));
	{ u128 x31 = ((x22 + ((u128)x25 * x19)) + ((u128)x28 * x18));
	{ u128 x32 = (x23 + ((u128)x25 * x18));
	{ u64 x33 = (u64) (x29 >> 0x33);
	{ u64 x34 = ((u64)x29 & 0x7ffffffffffff);
	{ u128 x35 = (x33 + x30);
	{ u64 x36 = (u64) (x35 >> 0x33);
	{ u64 x37 = ((u64)x35 & 0x7ffffffffffff);
	{ u128 x38 = (x36 + x31);
	{ u64 x39 = (u64) (x38 >> 0x33);
	{ u64 x40 = ((u64)x38 & 0x7ffffffffffff);
	{ u128 x41 = (x39 + x32);
	{ u64 x42 = (u64) (x41 >> 0x33);
	{ u64 x43 = ((u64)x41 & 0x7ffffffffffff);
	{ u128 x44 = (x42 + x24);
	{ u64 x45 = (u64) (x44 >> 0x33);
	{ u64 x46 = ((u64)x44 & 0x7ffffffffffff);
	{ u64 x47 = (x34 + (0x13 * x45));
	{ u64 x48 = (x47 >> 0x33);
	{ u64 x49 = (x47 & 0x7ffffffffffff);
	{ u64 x50 = (x48 + x37);
	{ u64 x51 = (x50 >> 0x33);
	{ u64 x52 = (x50 & 0x7ffffffffffff);
	out[0] = x49;
	out[1] = x52;
	out[2] = (x51 + x40);
	out[3] = x43;
	out[4] = x46;
	}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}

static __always_inline void fe_mul121666(fe *h, const fe_loose *f)
{
	fe_mul_121666_impl(h->v, f->v);
}

bool curve25519_fiat64(u8 out[CURVE25519_POINT_SIZE], const u8 scalar[CURVE25519_POINT_SIZE], const u8 point[CURVE25519_POINT_SIZE])
{
	fe x1, x2, z2, x3, z3, tmp0, tmp1;
	fe_loose x2l, z2l, x3l, tmp0l, tmp1l;
	unsigned swap = 0;
	int pos;
	u8 e[32];

	memcpy(e, scalar, 32);
	normalize_secret(e);

	/* The following implementation was transcribed to Coq and proven to
	 * correspond to unary scalar multiplication in affine coordinates given that
	 * x1 != 0 is the x coordinate of some point on the curve. It was also checked
	 * in Coq that doing a ladderstep with x1 = x3 = 0 gives z2' = z3' = 0, and z2
	 * = z3 = 0 gives z2' = z3' = 0. The statement was quantified over the
	 * underlying field, so it applies to Curve25519 itself and the quadratic
	 * twist of Curve25519. It was not proven in Coq that prime-field arithmetic
	 * correctly simulates extension-field arithmetic on prime-field values.
	 * The decoding of the byte array representation of e was not considered.
	 * Specification of Montgomery curves in affine coordinates:
	 * <https://github.com/mit-plv/fiat-crypto/blob/2456d821825521f7e03e65882cc3521795b0320f/src/Spec/MontgomeryCurve.v#L27>
	 * Proof that these form a group that is isomorphic to a Weierstrass curve:
	 * <https://github.com/mit-plv/fiat-crypto/blob/2456d821825521f7e03e65882cc3521795b0320f/src/Curves/Montgomery/AffineProofs.v#L35>
	 * Coq transcription and correctness proof of the loop (where scalarbits=255):
	 * <https://github.com/mit-plv/fiat-crypto/blob/2456d821825521f7e03e65882cc3521795b0320f/src/Curves/Montgomery/XZ.v#L118>
	 * <https://github.com/mit-plv/fiat-crypto/blob/2456d821825521f7e03e65882cc3521795b0320f/src/Curves/Montgomery/XZProofs.v#L278>
	 * preconditions: 0 <= e < 2^255 (not necessarily e < order), fe_invert(0) = 0
	 */
	fe_frombytes(&x1, point);
	fe_1(&x2);
	fe_0(&z2);
	fe_copy(&x3, &x1);
	fe_1(&z3);

	for (pos = 254; pos >= 0; --pos) {
		/* loop invariant as of right before the test, for the case where x1 != 0:
		 *   pos >= -1; if z2 = 0 then x2 is nonzero; if z3 = 0 then x3 is nonzero
		 *   let r := e >> (pos+1) in the following equalities of projective points:
		 *   to_xz (r*P)     === if swap then (x3, z3) else (x2, z2)
		 *   to_xz ((r+1)*P) === if swap then (x2, z2) else (x3, z3)
		 *   x1 is the nonzero x coordinate of the nonzero point (r*P-(r+1)*P)
		 */
		unsigned b = 1 & (e[pos / 8] >> (pos & 7));
		swap ^= b;
		fe_cswap(&x2, &x3, swap);
		fe_cswap(&z2, &z3, swap);
		swap = b;
		/* Coq transcription of ladderstep formula (called from transcribed loop):
		 * <https://github.com/mit-plv/fiat-crypto/blob/2456d821825521f7e03e65882cc3521795b0320f/src/Curves/Montgomery/XZ.v#L89>
		 * <https://github.com/mit-plv/fiat-crypto/blob/2456d821825521f7e03e65882cc3521795b0320f/src/Curves/Montgomery/XZProofs.v#L131>
		 * x1 != 0 <https://github.com/mit-plv/fiat-crypto/blob/2456d821825521f7e03e65882cc3521795b0320f/src/Curves/Montgomery/XZProofs.v#L217>
		 * x1  = 0 <https://github.com/mit-plv/fiat-crypto/blob/2456d821825521f7e03e65882cc3521795b0320f/src/Curves/Montgomery/XZProofs.v#L147>
		 */
		fe_sub(&tmp0l, &x3, &z3);
		fe_sub(&tmp1l, &x2, &z2);
		fe_add(&x2l, &x2, &z2);
		fe_add(&z2l, &x3, &z3);
		fe_mul_tll(&z3, &tmp0l, &x2l);
		fe_mul_tll(&z2, &z2l, &tmp1l);
		fe_sq_tl(&tmp0, &tmp1l);
		fe_sq_tl(&tmp1, &x2l);
		fe_add(&x3l, &z3, &z2);
		fe_sub(&z2l, &z3, &z2);
		fe_mul_ttt(&x2, &tmp1, &tmp0);
		fe_sub(&tmp1l, &tmp1, &tmp0);
		fe_sq_tl(&z2, &z2l);
		fe_mul121666(&z3, &tmp1l);
		fe_sq_tl(&x3, &x3l);
		fe_add(&tmp0l, &tmp0, &z3);
		fe_mul_ttt(&z3, &x1, &z2);
		fe_mul_tll(&z2, &tmp1l, &tmp0l);
	}
	/* here pos=-1, so r=e, so to_xz (e*P) === if swap then (x3, z3) else (x2, z2) */
	fe_cswap(&x2, &x3, swap);
	fe_cswap(&z2, &z3, swap);

	fe_invert(&z2, &z2);
	fe_mul_ttt(&x2, &x2, &z2);
	fe_tobytes(out, &x2);

	return true;
}
