/*
// SHA-256 a.k.a. SHA-2; computation over whole blocks only.
// Uses ARMv8/Aarch64 Cryptographic Extensions.
//
// Written by Romain Dolbeau (romain@dolbeau.org)
//
// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.
//
// In jurisdictions that recognize copyright laws, the author or authors
// of this software dedicate any and all copyright interest in the
// software to the public domain. We make this dedication for the benefit
// of the public at large and to the detriment of our heirs and
// successors. We intend this dedication to be an overt act of
// relinquishment in perpetuity of all present and future rights to this
// software under copyright law.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
// OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
// ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
// OTHER DEALINGS IN THE SOFTWARE.
//
// For more information, please refer to <http://unlicense.org/>
//
// The authors knows of no intellectual property claims relevant to this work.
*/

#include "crypto_hashblocks.h"

#include <arm_neon.h>

int crypto_hashblocks(unsigned char *statebytes,const unsigned char *in,unsigned long long inlen) {
	static unsigned int s256cst[64]= {
		0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
		0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
		0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
		0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
		0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
		0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
		0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
		0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
		0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
		0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
		0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
		0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
		0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
		0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
		0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
		0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 };
	unsigned long long pos = 0;
	/* load constants */
	uint32x4_t c0 = vld1q_u32(s256cst +  0);
	uint32x4_t c1 = vld1q_u32(s256cst +  4);
	uint32x4_t c2 = vld1q_u32(s256cst +  8);
	uint32x4_t c3 = vld1q_u32(s256cst + 12);
	uint32x4_t c4 = vld1q_u32(s256cst + 16);
	uint32x4_t c5 = vld1q_u32(s256cst + 20);
	uint32x4_t c6 = vld1q_u32(s256cst + 24);
	uint32x4_t c7 = vld1q_u32(s256cst + 28);
	uint32x4_t c8 = vld1q_u32(s256cst + 32);
	uint32x4_t c9 = vld1q_u32(s256cst + 36);
	uint32x4_t ca = vld1q_u32(s256cst + 40);
	uint32x4_t cb = vld1q_u32(s256cst + 44);
	uint32x4_t cc = vld1q_u32(s256cst + 48);
	uint32x4_t cd = vld1q_u32(s256cst + 52);
	uint32x4_t ce = vld1q_u32(s256cst + 56);
	uint32x4_t cf = vld1q_u32(s256cst + 60);
	/* load state */
	uint32x4_t d0 = vld1q_u32((uint32_t*)(statebytes +  0));
	uint32x4_t d1 = vld1q_u32((uint32_t*)(statebytes + 16));
	uint32x4_t s0, s1, h0, h1;
	/* make state big-endian */
	d0 = (uint32x4_t)vrev32q_u8((uint8x16_t)d0);
	d1 = (uint32x4_t)vrev32q_u8((uint8x16_t)d1);
	while (inlen >= 64) {
		/* load one block */
		uint32x4_t i0 = vld1q_u32((uint32_t*)(in+pos+ 0));
		uint32x4_t i1 = vld1q_u32((uint32_t*)(in+pos+16));
		uint32x4_t i2 = vld1q_u32((uint32_t*)(in+pos+32));
		uint32x4_t i3 = vld1q_u32((uint32_t*)(in+pos+48));
		uint32x4_t j0, j1, j2, j3;
		uint32x4_t x0, x1;
		
		/* copy state to working space */
		s0 = d0;
		s1 = d1;
		
		/* make block big-endian */
		i0 = (uint32x4_t)vrev32q_u8((uint8x16_t)i0);
		i1 = (uint32x4_t)vrev32q_u8((uint8x16_t)i1);
		i2 = (uint32x4_t)vrev32q_u8((uint8x16_t)i2);
		i3 = (uint32x4_t)vrev32q_u8((uint8x16_t)i3);

		/*
		 * This computes 16 rounds in i0..i3
		 * using 16 constants in c0..c3
		 * we need h0,h1,x0,x1 as scratch
		 */
#define DO16ROUNDS(i0, i1, i2, i3, c0, c1, c2, c3)	\
		h0 = vaddq_u32(i0, c0);			\
		x0 = vsha256hq_u32(s0, s1, h0);		\
		x1 = vsha256h2q_u32(s1, s0, h0);	\
		h1 = vaddq_u32(i1, c1);			\
		s0 = vsha256hq_u32(x0, x1, h1);		\
		s1 = vsha256h2q_u32(x1, x0, h1);	\
		h0 = vaddq_u32(i2, c2);			\
		x0 = vsha256hq_u32(s0, s1, h0);		\
		x1 = vsha256h2q_u32(s1, s0, h0);	\
		h1 = vaddq_u32(i3, c3);			\
		s0 = vsha256hq_u32(x0, x1, h1);		\
		s1 = vsha256h2q_u32(x1, x0, h1)

		/*
		 * this expands the block (or previously
		 * expanded) in i0..i3 to j0..j3
		 */
#define DO16EXPANDS(i0, i1, i2, i3, j0, j1, j2, j3)	\
		j0 = vsha256su0q_u32(i0, i1);		\
		j0 = vsha256su1q_u32(j0, i2, i3);	\
		j1 = vsha256su0q_u32(i1, i2);		\
		j1 = vsha256su1q_u32(j1, i3, j0);	\
		j2 = vsha256su0q_u32(i2, i3);		\
		j2 = vsha256su1q_u32(j2, j0, j1);	\
		j3 = vsha256su0q_u32(i3, j0);		\
		j3 = vsha256su1q_u32(j3, j1, j2)

		DO16ROUNDS(i0, i1, i2, i3, c0, c1, c2, c3);

		DO16EXPANDS(i0, i1, i2, i3, j0, j1, j2, j3);

		DO16ROUNDS(j0, j1, j2, j3, c4, c5, c6, c7);

		DO16EXPANDS(j0, j1, j2, j3, i0, i1, i2, i3);

		DO16ROUNDS(i0, i1, i2, i3, c8, c9, ca, cb);

		DO16EXPANDS(i0, i1, i2, i3, j0, j1, j2, j3);

		DO16ROUNDS(j0, j1, j2, j3, cc, cd, ce, cf);

		/* final add to update states */
		d0 = vaddq_u32(s0, d0);
		d1 = vaddq_u32(s1, d1);

		inlen -= 64;
		pos += 64;
	}

	/* store back to little-endian */
	d0 = (uint32x4_t)vrev32q_u8((uint8x16_t)d0);
	d1 = (uint32x4_t)vrev32q_u8((uint8x16_t)d1);
	vst1q_u32((uint32_t*)(statebytes +  0), d0);
	vst1q_u32((uint32_t*)(statebytes + 16), d1);

	return inlen;
}

