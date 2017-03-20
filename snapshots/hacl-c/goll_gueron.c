/* ChaCha implementation using 256-bit (512-bit) vectorization by the authors of [1].
* This is a public domain implementation, which improves the slightly modified implementations
* of Ted Krovetz in the Chromium Project by using the Advanced Vector Extensions AVX2 and AVX512
* to widen the vectorization. Further details and measurement results are provided in:
* [1] Goll, M., and Gueron,S.: Vectorization of ChaCha Stream Cipher. Cryptology ePrint Archive,
* Report 2013/759, November, 2013, http://eprint.iacr.org/2013/759.pdf
*/

#include <string.h>
#include <immintrin.h>

// round selector, specified values:
//  8:  low security - high speed
// 12:  mid security -  mid speed
// 20: high security -  low speed
#ifndef CHACHA_RNDS
#define CHACHA_RNDS 20
#endif

#ifdef __AVX2__
typedef unsigned vec128 __attribute__ ((vector_size (16)));
#define XOR128(a,b)	(vec128)_mm_xor_si128((__m128i)a, (__m128i)b)
#define LOAD128(m)	(vec128)_mm_loadu_si128((__m128i*)(m))
#define STORE128(m,r)	_mm_storeu_si128((__m128i*)(m), (__m128i) (r))
#define WRITE_XOR_128(ip, op, d, v0, v1, v2, v3)	\
    STORE128(op + d + 0, XOR128(LOAD128(ip + d + 0), v0));	\
    STORE128(op + d + 4, XOR128(LOAD128(ip + d + 4), v1));	\
    STORE128(op + d + 8, XOR128(LOAD128(ip + d + 8), v2));	\
    STORE128(op + d +12, XOR128(LOAD128(ip + d +12), v3));
typedef unsigned vec256 __attribute__ ((vector_size (32)));
#define TWO	_mm256_set_epi64x(0,2,0,2)
#define LOAD256(m)		(vec256)_mm256_loadu_si256((__m256i*)(m))
#define STORE256(m,r)	_mm256_storeu_si256((__m256i*)(m), (__m256i) (r))
#define LOW128(x)	(vec128)_mm256_castsi256_si128((__m256i) (x))
#define HIGH128(x)	(vec128)_mm256_extractf128_si256((__m256i) (x), 1)
#define ADD256_32(a,b)	(vec256)_mm256_add_epi32((__m256i)a, (__m256i)b)
#define ADD256_64(a,b)	(vec256)_mm256_add_epi64((__m256i)a, (__m256i)b)
#define XOR256(a,b)	(vec256)_mm256_xor_si256((__m256i)a, (__m256i)b)
#define ROR256_V1(x)	(vec256)_mm256_shuffle_epi32((__m256i)x,_MM_SHUFFLE(0,3,2,1))
#define ROR256_V2(x)	(vec256)_mm256_shuffle_epi32((__m256i)x,_MM_SHUFFLE(1,0,3,2))
#define ROR256_V3(x)	(vec256)_mm256_shuffle_epi32((__m256i)x,_MM_SHUFFLE(2,1,0,3))
#define ROL256_7(x)		XOR256(_mm256_slli_epi32((__m256i)x, 7), _mm256_srli_epi32((__m256i)x,25))
#define ROL256_12(x)	XOR256(_mm256_slli_epi32((__m256i)x,12), _mm256_srli_epi32((__m256i)x,20))

#define ROL256_8(x)		(vec256)_mm256_shuffle_epi8((__m256i)x,_mm256_set_epi8(14,13,12,15,	\
																			   10, 9, 8,11,	\
																				6, 5, 4, 7,	\
																				2, 1, 0, 3,	\
																			   14,13,12,15,	\
																			   10, 9, 8,11,	\
																				6, 5, 4, 7,	\
										       2, 1, 0, 3))

#define ROL256_16(x)	(vec256)_mm256_shuffle_epi8((__m256i)x,_mm256_set_epi8(13,12,15,14,	\
																				9, 8,11,10,	\
																				5, 4, 7, 6,	\
																				1, 0, 3, 2,	\
																			   13,12,15,14,	\
																			    9, 8,11,10,	\
																			    5, 4, 7, 6,	\
																			    1, 0, 3, 2))
#define DQROUND_VECTORS_256(a,b,c,d)						\
    a = ADD256_32(a,b); d = XOR256(d,a); d = ROL256_16(d);	\
    c = ADD256_32(c,d); b = XOR256(b,c); b = ROL256_12(b);	\
    a = ADD256_32(a,b); d = XOR256(d,a); d = ROL256_8(d);	\
    c = ADD256_32(c,d); b = XOR256(b,c); b = ROL256_7(b);	\
    b = ROR256_V1(b); c = ROR256_V2(c); d = ROR256_V3(d);	\
    a = ADD256_32(a,b); d = XOR256(d,a); d = ROL256_16(d);	\
    c = ADD256_32(c,d); b = XOR256(b,c); b = ROL256_12(b);	\
    a = ADD256_32(a,b); d = XOR256(d,a); d = ROL256_8(d);	\
    c = ADD256_32(c,d); b = XOR256(b,c); b = ROL256_7(b);	\
    b = ROR256_V3(b); c = ROR256_V2(c); d = ROR256_V1(d);
#define WRITE_XOR_256(ip, op, d, v0, v1, v2, v3)							\
    STORE256(op + d + 0, XOR256(LOAD256(ip + d + 0), _mm256_permute2x128_si256((__m256i)v0, (__m256i)v1, 0x20)));	\
    STORE256(op + d + 8, XOR256(LOAD256(ip + d + 8), _mm256_permute2x128_si256((__m256i)v2, (__m256i)v3, 0x20)));	\
    STORE256(op + d +16, XOR256(LOAD256(ip + d +16), _mm256_permute2x128_si256((__m256i)v0, (__m256i)v1, 0x31)));	\
	STORE256(op + d +24, XOR256(LOAD256(ip + d +24), _mm256_permute2x128_si256((__m256i)v2, (__m256i)v3, 0x31)));
#ifdef __AVX512F__
typedef unsigned vec512 __attribute__ ((vector_size (64)));
typedef long long __m512i __attribute__ ((__vector_size__ (64), __may_alias__));
#define FOUR	_mm512_set_epi64(0,4,0,4,0,4,0,4)
#define LOAD512(m)		(vec512)_mm512_loadu_si512((__m512i*)(m))
#define STORE512(m,r)	_mm512_storeu_si512((__m512i*)(m), (__m512i) (r))
#define LOW256(x)	(vec256)_mm512_extracti64x4_epi64((__m512i) (x), 0)
#define HIGH256(x)	(vec256)_mm512_extracti64x4_epi64((__m512i) (x), 1)
#define ADD512_32(a,b)	(vec512)_mm512_add_epi32((__m512i)a, (__m512i)b)
#define ADD512_64(a,b)	(vec512)_mm512_add_epi64((__m512i)a, (__m512i)b)
#define XOR512(a,b)	(vec512)_mm512_xor_si512((__m512i)a, (__m512i)b)
#define ROR512_V1(x)	(vec512)_mm512_shuffle_epi32((__m512i)x,_MM_SHUFFLE(0,3,2,1))
#define ROR512_V2(x)	(vec512)_mm512_shuffle_epi32((__m512i)x,_MM_SHUFFLE(1,0,3,2))
#define ROR512_V3(x)	(vec512)_mm512_shuffle_epi32((__m512i)x,_MM_SHUFFLE(2,1,0,3))
#define ROL512(x,b)		(vec512)_mm512_rol_epi32((__m512i)x, b)
#define DQROUND_VECTORS_512(a,b,c,d)						\
    a = ADD512_32(a,b); d = XOR512(d,a); d = ROL512(d,16);	\
    c = ADD512_32(c,d); b = XOR512(b,c); b = ROL512(b,12);	\
    a = ADD512_32(a,b); d = XOR512(d,a); d = ROL512(d, 8);	\
    c = ADD512_32(c,d); b = XOR512(b,c); b = ROL512(b, 7);	\
    b = ROR512_V1(b); c = ROR512_V2(c); d = ROR512_V3(d);	\
    a = ADD512_32(a,b); d = XOR512(d,a); d = ROL512(d,16);	\
    c = ADD512_32(c,d); b = XOR512(b,c); b = ROL512(b,12);	\
    a = ADD512_32(a,b); d = XOR512(d,a); d = ROL512(d, 8);	\
    c = ADD512_32(c,d); b = XOR512(b,c); b = ROL512(b, 7);	\
    b = ROR512_V3(b); c = ROR512_V2(c); d = ROR512_V1(d);
#define WRITE_XOR_512(ip, op, d, v0, v1, v2, v3)																		\
	STORE512(op + d + 0, XOR512(LOAD512(ip + d + 0),																	\
			_mm512_mask_mov_epi32(_mm512_permutexvar_epi64((__m512i)(v3), _mm512_set_epi64(1,0,7,6,5,4,3,2)), 0x0fff,	\
			_mm512_mask_mov_epi32(_mm512_permutexvar_epi64((__m512i)(v2), _mm512_set_epi64(3,2,1,0,7,6,5,4)), 0xf0ff,	\
			_mm512_mask_mov_epi32(_mm512_permutexvar_epi64((__m512i)(v1), _mm512_set_epi64(5,4,3,2,1,0,7,6)), 0xff0f,	\
			(__m512i)(v0))))));																							\
	STORE512(op + d +16, XOR512(LOAD512(ip + d +16),																	\
			_mm512_mask_mov_epi32(_mm512_permutexvar_epi64((__m512i)(v3), _mm512_set_epi64(3,2,1,0,7,6,5,4)), 0x0fff,	\
			_mm512_mask_mov_epi32(_mm512_permutexvar_epi64((__m512i)(v2), _mm512_set_epi64(5,4,3,2,1,0,7,6)), 0xf0ff,	\
			_mm512_mask_mov_epi32(_mm512_permutexvar_epi64((__m512i)(v0), _mm512_set_epi64(1,0,7,6,5,4,3,2)), 0xfff0,	\
			(__m512i)(v1))))));																							\
	STORE512(op + d +32, XOR512(LOAD512(ip + d +32),																	\
			_mm512_mask_mov_epi32(_mm512_permutexvar_epi64((__m512i)(v3), _mm512_set_epi64(5,4,3,2,1,0,7,6)), 0x0fff,	\
			_mm512_mask_mov_epi32(_mm512_permutexvar_epi64((__m512i)(v1), _mm512_set_epi64(1,0,7,6,5,4,3,2)), 0xff0f,	\
			_mm512_mask_mov_epi32(_mm512_permutexvar_epi64((__m512i)(v0), _mm512_set_epi64(3,2,1,0,7,6,5,4)), 0xfff0,	\
			(__m512i)(v2))))));																							\
	STORE512(op + d +48, XOR512(LOAD512(ip + d +48),																	\
			_mm512_mask_mov_epi32(_mm512_permutexvar_epi64((__m512i)(v2), _mm512_set_epi64(1,0,7,6,5,4,3,2)), 0xf0ff,	\
			_mm512_mask_mov_epi32(_mm512_permutexvar_epi64((__m512i)(v1), _mm512_set_epi64(3,2,1,0,7,6,5,4)), 0xff0f,	\
			_mm512_mask_mov_epi32(_mm512_permutexvar_epi64((__m512i)(v0), _mm512_set_epi64(5,4,3,2,1,0,7,6)), 0xfff0,	\
			(__m512i)(v3))))));
#endif
#else
#error -- Implementation supports only microarchitectures with support for Advanced Vector Extensions (AVX2 or AVX512).
#endif

// Change * and ** to 'unsigned long long' if there is a need to encrypt/decrypt more than 2^32-1 bytes (~4GB) using a single call.
// This will slightly slow down the implementation due to all loop iterators become 64-bit.
int chacha_xor_avx(
		unsigned char *out,
		const unsigned char *in,
		unsigned int inlen, // *
		const unsigned char *nonce,
		const unsigned char *key,
		const unsigned long long counter
	)
{
#ifdef __AVX2__
	unsigned int i, j; // **
	unsigned int *op=(unsigned int *)out, *ip=(unsigned int *)in;

	__attribute__ ((aligned (16))) unsigned int chacha_const[] = {
		0x61707865,0x3320646E,0x79622D32,0x6B206574
	};

	vec128 s3 = (vec128) {
	  (unsigned int) counter,((unsigned int *)nonce)[0], ((unsigned int *)nonce)[1], ((unsigned int *)nonce)[2]
	};
#else
	return 1;
#endif

	vec256 d0, d1, d2, d3;
	d0 = (vec256)_mm256_broadcastsi128_si256(*(__m128i*)chacha_const);
	d1 = (vec256)_mm256_broadcastsi128_si256(((__m128i*)key)[0]);
	d2 = (vec256)_mm256_broadcastsi128_si256(((__m128i*)key)[1]);
	d3 = ADD256_64(_mm256_broadcastsi128_si256((__m128i)s3), _mm256_set_epi64x(0,1,0,0));

	for (j=0; j < inlen/384; j++) {
		vec256 v0=d0, v1=d1, v2=d2, v3=d3;
		vec256 v4=d0, v5=d1, v6=d2, v7=ADD256_64(d3, TWO);
		vec256 v8=d0, v9=d1, v10=d2, v11=ADD256_64(v7, TWO);

		for (i = CHACHA_RNDS/2; i; i--) {
			DQROUND_VECTORS_256(v0,v1,v2,v3)
			DQROUND_VECTORS_256(v4,v5,v6,v7)
			DQROUND_VECTORS_256(v8,v9,v10,v11)
		}

		WRITE_XOR_256(ip, op, 0, ADD256_32(v0,d0), ADD256_32(v1,d1), ADD256_32(v2,d2), ADD256_32(v3,d3))
		d3 = ADD256_64(d3, TWO);
		WRITE_XOR_256(ip, op,32, ADD256_32(v4,d0), ADD256_32(v5,d1), ADD256_32(v6,d2), ADD256_32(v7,d3))
		d3 = ADD256_64(d3, TWO);
		WRITE_XOR_256(ip, op,64, ADD256_32(v8,d0), ADD256_32(v9,d1), ADD256_32(v10,d2), ADD256_32(v11,d3))
		d3 = ADD256_64(d3, TWO);

		ip += 96;
		op += 96;
	}
	inlen = inlen % 384;

	if(inlen >= 256) {
		vec256 v0=d0, v1=d1, v2=d2, v3=d3;
		vec256 v4=d0, v5=d1, v6=d2, v7=ADD256_64(d3, TWO);

		for (i = CHACHA_RNDS/2; i; i--) {
			DQROUND_VECTORS_256(v0,v1,v2,v3)
			DQROUND_VECTORS_256(v4,v5,v6,v7)
		}

		WRITE_XOR_256(ip, op, 0, ADD256_32(v0,d0), ADD256_32(v1,d1), ADD256_32(v2,d2), ADD256_32(v3,d3))
		d3 = ADD256_64(d3, TWO);
		WRITE_XOR_256(ip, op,32, ADD256_32(v4,d0), ADD256_32(v5,d1), ADD256_32(v6,d2), ADD256_32(v7,d3))
		d3 = ADD256_64(d3, TWO);

		ip += 64;
		op += 64;

		inlen = inlen % 256;
	}

	if (inlen >= 128) {
		vec256 v0=d0, v1=d1, v2=d2, v3=d3;

		for (i = CHACHA_RNDS/2; i; i--) {
			DQROUND_VECTORS_256(v0,v1,v2,v3)
		}

		WRITE_XOR_256(ip, op, 0, ADD256_32(v0,d0), ADD256_32(v1,d1), ADD256_32(v2,d2), ADD256_32(v3,d3))
		d3 = ADD256_64(d3, TWO);

		ip += 32;
		op += 32;

		inlen = inlen % 128;
	}

	if (inlen) {
		vec256 v0=d0, v1=d1, v2=d2, v3=d3;
		__attribute__ ((aligned (16))) vec128 buf[4];

		for (i = CHACHA_RNDS/2; i; i--) {
			DQROUND_VECTORS_256(v0,v1,v2,v3)
		}
		v0 = ADD256_32(v0,d0); v1 = ADD256_32(v1,d1);
		v2 = ADD256_32(v2,d2); v3 = ADD256_32(v3,d3);

		if (inlen >= 64) {
			WRITE_XOR_128(ip, op, 0, LOW128(v0), LOW128(v1), LOW128(v2), LOW128(v3));
			buf[0] = HIGH128(v0); j = 64;
			if (inlen >= 80) {
				STORE128(op + 16, XOR128(LOAD128(ip + 16), buf[0]));
				buf[1] = HIGH128(v1);
				if (inlen >= 96) {
					STORE128(op + 20, XOR128(LOAD128(ip + 20), buf[1]));
					buf[2] = HIGH128(v2);
					if (inlen >= 112) {
						STORE128(op + 24, XOR128(LOAD128(ip + 24), buf[2]));
						buf[3] = HIGH128(v3);
					}
				}
			}
		} else {
			buf[0] = LOW128(v0);  j = 0;
			if (inlen >= 16) {
				STORE128(op + 0, XOR128(LOAD128(ip + 0), buf[0]));
				buf[1] = LOW128(v1);
				if (inlen >= 32) {
					STORE128(op + 4, XOR128(LOAD128(ip + 4), buf[1]));
					buf[2] = LOW128(v2);
					if (inlen >= 48) {
						STORE128(op + 8, XOR128(LOAD128(ip + 8), buf[2]));
						buf[3] = LOW128(v3);
					}
				}
			}
		}

		for (i=(inlen & ~15); i<inlen; i++) {
			((unsigned char *)op)[i] = ((unsigned char *)ip)[i] ^ ((unsigned char *)buf)[i-j];
		}
	}

	return 0;
}

int crypto_stream_xor(
		unsigned char *out,
		const unsigned char *in,
		unsigned long long inlen,
		const unsigned char *n,
		const unsigned char *k
		)
{
	return chacha_xor_avx(out,in,inlen,n,k,0);
}

int crypto_stream_xor_ic(
		unsigned char *out,
		const unsigned char *in,
		unsigned long long inlen,
		const unsigned char *n,
		const unsigned char *k,
		unsigned int ctr
		)
{
	return chacha_xor_avx(out,in,inlen,n,k,ctr);
}

int crypto_stream(
      unsigned char *out,
      unsigned long long outlen,
      const unsigned char *n,
      const unsigned char *k
    )
{
	memset(out,0,outlen);
	return chacha_xor_avx(out,out,outlen,n,k,0);
}

