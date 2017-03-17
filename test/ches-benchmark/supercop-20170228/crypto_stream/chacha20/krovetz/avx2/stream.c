/* Chacha implementation for Intel's AVX2 by Ted Krovetz (ted@krovetz.net).
 * Public domain.                                     Modified: 2013.06.19.
 * Chacha is an improvement on the stream cipher Salsa, described at
 * http://cr.yp.to/papers.html#chacha
 */
#include "crypto_stream.h"
#include <string.h>
#include <immintrin.h>

#ifndef CHACHA_RNDS
#define CHACHA_RNDS 20    /* 8 (high speed), 20 (conservative), 12 (middle) */
#endif

#define ADD(x,y)  _mm256_add_epi32(x,y)
#define XOR(x,y)  _mm256_xor_si256(x,y)
#define INC(x)    _mm256_add_epi32(x, _mm256_set_epi32(0,0,0,2,0,0,0,2))
#define ROTV1(x)  _mm256_shuffle_epi32(x,_MM_SHUFFLE(0,3,2,1))
#define ROTV2(x)  _mm256_shuffle_epi32(x,_MM_SHUFFLE(1,0,3,2))
#define ROTV3(x)  _mm256_shuffle_epi32(x,_MM_SHUFFLE(2,1,0,3))
#define ROTW7(x)  XOR(_mm256_slli_epi32(x, 7), _mm256_srli_epi32(x,25))
#define ROTW12(x) XOR(_mm256_slli_epi32(x,12), _mm256_srli_epi32(x,20))
#define ROTW8(x)  _mm256_shuffle_epi8(x,_mm256_set_epi8                     \
                        (14,13,12,15,10,9,8,11,6,5,4,7,2,1,0,3,             \
                        30,29,28,31,26,25,24,27,22,21,20,23,18,17,16,19))
#define ROTW16(x) _mm256_shuffle_epi8(x,_mm256_set_epi8                     \
                        (13,12,15,14,9,8,11,10,5,4,7,6,1,0,3,2,             \
                        29,28,31,30,25,24,27,26,21,20,23,22,17,16,19,18))
#define XOR_WRITE(d,s,x)  _mm256_storeu_si256((__m256i *)(d),               \
                          XOR(_mm256_loadu_si256((__m256i *)(s)), x))
#define DQROUND(a,b,c,d)                                                    \
    a = ADD(a,b); d = XOR(d,a); d = ROTW16(d);                              \
    c = ADD(c,d); b = XOR(b,c); b = ROTW12(b);                              \
    a = ADD(a,b); d = XOR(d,a); d = ROTW8(d);                               \
    c = ADD(c,d); b = XOR(b,c); b = ROTW7(b);                               \
    b = ROTV1(b); c = ROTV2(c); d = ROTV3(d);                               \
    a = ADD(a,b); d = XOR(d,a); d = ROTW16(d);                              \
    c = ADD(c,d); b = XOR(b,c); b = ROTW12(b);                              \
    a = ADD(a,b); d = XOR(d,a); d = ROTW8(d);                               \
    c = ADD(c,d); b = XOR(b,c); b = ROTW7(b);                               \
    b = ROTV3(b); c = ROTV2(c); d = ROTV1(d);

__attribute__ ((aligned (32)))
static const unsigned char sigma[16] = "expand 32-byte k";

int crypto_stream_xor(
        unsigned char *out,
        const unsigned char *in,
        unsigned long long inlen,
        const unsigned char *n,
        const unsigned char *k
)
{
    unsigned i;
    __m256i v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11;
    #if __clang__
    __m256i s0 = _mm_broadcastsi128_si256((__m128i *)sigma);
    #else
    __m256i s0 = _mm256_broadcastsi128_si256(*(__m128i *)sigma);
    #endif
    __m256i s1 = _mm256_loadu_si256((__m256i *)k);
    __m256i s2 = _mm256_permute2x128_si256(s1,s1,0x11);
    s1 = _mm256_permute2x128_si256(s1,s1,0x00);
    __m256i s3 = _mm256_or_si256(
        _mm256_slli_si256(_mm256_broadcastq_epi64(*(__m128i *)n), 8),
        _mm256_set_epi32(0,0,0,1,0,0,0,0)
    );
    while (inlen >= 3*128) {
        v8  = v4 = v0 = s0; v9 = v5 = v1 = s1;
        v10 = v6 = v2 = s2; v3 = s3; v7  = INC(v3); v11 = INC(v7);
        for (i = CHACHA_RNDS/2; i; i--) {
            DQROUND(v0,v1,v2,v3)
            DQROUND(v4,v5,v6,v7)
            DQROUND(v8,v9,v10,v11)
        }
        v0 = ADD(v0,s0); v1 = ADD(v1,s1); v2 = ADD(v2,s2); v3 = ADD(v3,s3);
        XOR_WRITE(out+ 0, in+ 0, _mm256_permute2x128_si256(v0,v1,0x20));
        XOR_WRITE(out+32, in+32, _mm256_permute2x128_si256(v2,v3,0x20));
        XOR_WRITE(out+64, in+64, _mm256_permute2x128_si256(v0,v1,0x31));
        XOR_WRITE(out+96, in+96, _mm256_permute2x128_si256(v2,v3,0x31));
        s3 = INC(s3);
        v4 = ADD(v4,s0); v5 = ADD(v5,s1); v6 = ADD(v6,s2); v7 = ADD(v7,s3);
        XOR_WRITE(out+128, in+128, _mm256_permute2x128_si256(v4,v5,0x20));
        XOR_WRITE(out+160, in+160, _mm256_permute2x128_si256(v6,v7,0x20));
        XOR_WRITE(out+192, in+192, _mm256_permute2x128_si256(v4,v5,0x31));
        XOR_WRITE(out+224, in+224, _mm256_permute2x128_si256(v6,v7,0x31));
        s3 = INC(s3);
        v8 = ADD(v8,s0); v9 = ADD(v9,s1); v10 = ADD(v10,s2); v11 = ADD(v11,s3);
        XOR_WRITE(out+256, in+256, _mm256_permute2x128_si256(v8,v9,0x20));
        XOR_WRITE(out+288, in+288, _mm256_permute2x128_si256(v10,v11,0x20));
        XOR_WRITE(out+320, in+320, _mm256_permute2x128_si256(v8,v9,0x31));
        XOR_WRITE(out+352, in+352, _mm256_permute2x128_si256(v10,v11,0x31));
        s3 = INC(s3);
        inlen -= 3*128;
        in += 3*128;
        out += 3*128;
    }
#if 1
    if (inlen >= 2*128) {
        v4 = v0 = s0; v5 = v1 = s1;
        v6 = v2 = s2; v3 = s3; v7 = INC(v3);
        for (i = CHACHA_RNDS/2; i; i--) {
            DQROUND(v0,v1,v2,v3)
            DQROUND(v4,v5,v6,v7)
        }
        v0 = ADD(v0,s0); v1 = ADD(v1,s1); v2 = ADD(v2,s2); v3 = ADD(v3,s3);
        XOR_WRITE(out+ 0, in+ 0, _mm256_permute2x128_si256(v0,v1,0x20));
        XOR_WRITE(out+32, in+32, _mm256_permute2x128_si256(v2,v3,0x20));
        XOR_WRITE(out+64, in+64, _mm256_permute2x128_si256(v0,v1,0x31));
        XOR_WRITE(out+96, in+96, _mm256_permute2x128_si256(v2,v3,0x31));
        s3 = INC(s3);
        v4 = ADD(v4,s0); v5 = ADD(v5,s1); v6 = ADD(v6,s2); v7 = ADD(v7,s3);
        XOR_WRITE(out+128, in+128, _mm256_permute2x128_si256(v4,v5,0x20));
        XOR_WRITE(out+160, in+160, _mm256_permute2x128_si256(v6,v7,0x20));
        XOR_WRITE(out+192, in+192, _mm256_permute2x128_si256(v4,v5,0x31));
        XOR_WRITE(out+224, in+224, _mm256_permute2x128_si256(v6,v7,0x31));
        s3 = INC(s3);
        inlen -= 2*128;
        in += 2*128;
        out += 2*128;
    }
#endif
    while (inlen >= 128) {
        v0 = s0; v1 = s1; v2 = s2; v3 = s3;
        for (i = CHACHA_RNDS/2; i; i--) {
            DQROUND(v0,v1,v2,v3)
        }
        v0 = ADD(v0,s0); v1 = ADD(v1,s1); v2 = ADD(v2,s2); v3 = ADD(v3,s3);
        XOR_WRITE(out+ 0, in+ 0, _mm256_permute2x128_si256(v0,v1,0x20));
        XOR_WRITE(out+32, in+32, _mm256_permute2x128_si256(v2,v3,0x20));
        XOR_WRITE(out+64, in+64, _mm256_permute2x128_si256(v0,v1,0x31));
        XOR_WRITE(out+96, in+96, _mm256_permute2x128_si256(v2,v3,0x31));
        s3 = INC(s3);
        inlen -= 128;
        in += 1*128;
        out += 1*128;
    }
    if (inlen > 0) {
        __m256i tail;
        __attribute__ ((aligned (32))) char buf[32];

        v0 = s0; v1 = s1; v2 = s2; v3 = s3;
        for (i = CHACHA_RNDS/2; i; i--) {
            DQROUND(v0,v1,v2,v3)
        }
        v0 = ADD(v0,s0); v1 = ADD(v1,s1); v2 = ADD(v2,s2); v3 = ADD(v3,s3);
        s0 = _mm256_permute2x128_si256(v0,v1,0x20);
        s1 = _mm256_permute2x128_si256(v2,v3,0x20);
        s2 = _mm256_permute2x128_si256(v0,v1,0x31);
        s3 = _mm256_permute2x128_si256(v2,v3,0x31);
        if (inlen >= 64) {
            XOR_WRITE(out+0, in+0, s0);
            XOR_WRITE(out+32, in+32, s1);
            if (inlen >= 96) {
                XOR_WRITE(out+64, in+64, s2);
                tail = s3; out += 96; in += 96; inlen -= 96;
            } else { tail =s2; out += 64; in += 64; inlen -= 64; }
        } else if (inlen >= 32) {
            XOR_WRITE(out+0, in+0, s0);
            tail = s1; out += 32; in += 32; inlen -= 32;
        } else tail = s0;
        memcpy(buf,in,inlen);
        *(__m256i *)buf = XOR(tail, *(__m256i *)buf);
        memcpy(out,buf,inlen);
    }
    return 0;
}

int crypto_stream(
                                  unsigned char *out,
                                  unsigned long long outlen,
                                  const unsigned char *n,
                                  const unsigned char *k
                                  )
{
    memset(out,0,outlen);
    return crypto_stream_xor(out,out,outlen,n,k);
}
