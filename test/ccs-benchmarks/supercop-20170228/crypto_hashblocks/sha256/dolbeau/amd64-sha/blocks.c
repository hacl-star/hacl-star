/*
// SHA-256 a.k.a. SHA-2; computation over whole blocks only.
// Uses Intel SHA Extension.
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

#include <immintrin.h>

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
	static unsigned long long perm[2] = { 0x0405060700010203ull,
					      0x0C0D0E0F08090A0Bull
	};
	__m128i vperm;
	unsigned long long pos = 0;
	/* Load constants */
	__m128i c0 = _mm_loadu_si128((const __m128i*)(s256cst +  0));
	__m128i c1 = _mm_loadu_si128((const __m128i*)(s256cst +  4));
	__m128i c2 = _mm_loadu_si128((const __m128i*)(s256cst +  8));
	__m128i c3 = _mm_loadu_si128((const __m128i*)(s256cst + 12));
	__m128i c4 = _mm_loadu_si128((const __m128i*)(s256cst + 16));
	__m128i c5 = _mm_loadu_si128((const __m128i*)(s256cst + 20));
	__m128i c6 = _mm_loadu_si128((const __m128i*)(s256cst + 24));
	__m128i c7 = _mm_loadu_si128((const __m128i*)(s256cst + 28));
	__m128i c8 = _mm_loadu_si128((const __m128i*)(s256cst + 32));
	__m128i c9 = _mm_loadu_si128((const __m128i*)(s256cst + 36));
	__m128i ca = _mm_loadu_si128((const __m128i*)(s256cst + 40));
	__m128i cb = _mm_loadu_si128((const __m128i*)(s256cst + 44));
	__m128i cc = _mm_loadu_si128((const __m128i*)(s256cst + 48));
	__m128i cd = _mm_loadu_si128((const __m128i*)(s256cst + 52));
	__m128i ce = _mm_loadu_si128((const __m128i*)(s256cst + 56));
	__m128i cf = _mm_loadu_si128((const __m128i*)(s256cst + 60));
	vperm = _mm_loadu_si128((const __m128i*)(perm));
	/* load state */
	__m128i d0 = _mm_loadu_si128((const __m128i*)(statebytes +  0));
	__m128i d1 = _mm_loadu_si128((const __m128i*)(statebytes + 16));
	__m128i s0, s1, h0, h1;
	/* make state big-endian */
	d0 = _mm_shuffle_epi8(d0, vperm);
	d1 = _mm_shuffle_epi8(d1, vperm);
	/*
	 * Weird Intel ordering
	 * For some reason, Intel instructions
	 * need the data in the hash reordered
	 * from (DCBA, HGFE) [d0,d1] to
	 * (ABEF, CDGH) [d0, d1] ...
	 */
	d0 = _mm_shuffle_epi32(d0, 0xb1);
	d1 = _mm_shuffle_epi32(d1, 0x1b);
	s0 = d0;
	d0 = _mm_alignr_epi8(d0, d1, 0x08);
	d1 = _mm_blend_epi16(d1, s0, 0xf0);
	while (inlen >= 64) {
		/* load one block */
		__m128i i0 = _mm_loadu_si128((const __m128i*)(in+pos+ 0));
		__m128i i1 = _mm_loadu_si128((const __m128i*)(in+pos+16));
		__m128i i2 = _mm_loadu_si128((const __m128i*)(in+pos+32));
		__m128i i3 = _mm_loadu_si128((const __m128i*)(in+pos+48));
		__m128i j0, j1, j2, j3;
		__m128i x0, x1;
		
		/* copy state to working space */
		s0 = d0;
		s1 = d1;
		
		/* make block big-endian */
		i0 = _mm_shuffle_epi8(i0, vperm);
		i1 = _mm_shuffle_epi8(i1, vperm);
		i2 = _mm_shuffle_epi8(i2, vperm);
		i3 = _mm_shuffle_epi8(i3, vperm);

		/*
		 * This computes 16 rounds in i0..i3
		 * using 16 constants in c0..c3
		 * We need h0,h1,x0,x1 as scratch
		 * Each pair of rounds done by sha256rnds2
		 * only work on 64 bits from the third operand,
		 * so we need the shuffle to access the upper
		 * half of the data
		 */
#define DO16ROUNDS(i0, i1, i2, i3, c0, c1, c2, c3)	\
		h0 = _mm_add_epi32(i0, c0);		\
		x1 = _mm_sha256rnds2_epu32(s1, s0, h0);	\
		h0 = _mm_shuffle_epi32(h0, 0x0e);	\
		x0 = _mm_sha256rnds2_epu32(s0, x1, h0);	\
							\
		h1 = _mm_add_epi32(i1, c1);		\
		s1 = _mm_sha256rnds2_epu32(x1, x0, h1);	\
		h1 = _mm_shuffle_epi32(h1, 0x0e);	\
		s0 = _mm_sha256rnds2_epu32(x0, s1, h1);	\
							\
		h0 = _mm_add_epi32(i2, c2);		\
		x1 = _mm_sha256rnds2_epu32(s1, s0, h0);	\
		h0 = _mm_shuffle_epi32(h0, 0x0e);	\
		x0 = _mm_sha256rnds2_epu32(s0, x1, h0);	\
							\
		h1 = _mm_add_epi32(i3, c3);		\
		s1 = _mm_sha256rnds2_epu32(x1, x0, h1);	\
		h1 = _mm_shuffle_epi32(h1, 0x0e);	\
		s0 = _mm_sha256rnds2_epu32(x0, s1, h1)

		/*
		 * This expands the block (or previously
		 * expanded) in i0..i3 to j0..j3
		 * We need to move data around to do
		 * one of the addition that isn't
		 * performed by either sha instructions.
		 */
#define DO16EXPANDS(i0, i1, i2, i3, j0, j1, j2, j3)	\
		j0 = _mm_sha256msg1_epu32(i0, i1);	\
		h0 = _mm_alignr_epi8(i3, i2, 0x04);	\
		j0 = _mm_add_epi32(j0, h0);		\
		j0 = _mm_sha256msg2_epu32(j0, i3);	\
							\
		j1 = _mm_sha256msg1_epu32(i1, i2);	\
		h0 = _mm_alignr_epi8(j0, i3, 0x04);	\
		j1 = _mm_add_epi32(j1, h0);		\
		j1 = _mm_sha256msg2_epu32(j1, j0);	\
							\
		j2 = _mm_sha256msg1_epu32(i2, i3);	\
		h0 = _mm_alignr_epi8(j1, j0, 0x04);	\
		j2 = _mm_add_epi32(j2, h0);		\
		j2 = _mm_sha256msg2_epu32(j2, j1);	\
							\
		j3 = _mm_sha256msg1_epu32(i3, j0);	\
		h0 = _mm_alignr_epi8(j2, j1, 0x04);	\
		j3 = _mm_add_epi32(j3, h0);		\
		j3 = _mm_sha256msg2_epu32(j3, j2)

		DO16ROUNDS(i0, i1, i2, i3, c0, c1, c2, c3);

		DO16EXPANDS(i0, i1, i2, i3, j0, j1, j2, j3);

		DO16ROUNDS(j0, j1, j2, j3, c4, c5, c6, c7);

		DO16EXPANDS(j0, j1, j2, j3, i0, i1, i2, i3);

		DO16ROUNDS(i0, i1, i2, i3, c8, c9, ca, cb);

		DO16EXPANDS(i0, i1, i2, i3, j0, j1, j2, j3);

		DO16ROUNDS(j0, j1, j2, j3, cc, cd, ce, cf);

		/* final add to update states */
		d0 = _mm_add_epi32(s0, d0);
		d1 = _mm_add_epi32(s1, d1);

		inlen -= 64;
		pos += 64;
	}

	/* Undo weird Intel ordering */
	d0 = _mm_shuffle_epi32(d0, 0xb1);
	d1 = _mm_shuffle_epi32(d1, 0x1b);
	s0 = d0;
	d0 = _mm_alignr_epi8(d1, d0, 0x08);
	d1 = _mm_blend_epi16(s0, d1, 0xf0);
	/* Store back to little-endian */
	d0 = _mm_shuffle_epi8(d0, vperm);
	d1 = _mm_shuffle_epi8(d1, vperm);
	_mm_storeu_si128((__m128i*)(statebytes +  0), d0);
	_mm_storeu_si128((__m128i*)(statebytes + 16), d1);

	return inlen;
}
