/* Chacha implementation for 16-byte vectors by Ted Krovetz (ted@krovetz.net).
 * Assumes 32-bit int, 64-bit long long. Public domain. Modified: 2013.06.19.
 * Chacha is an improvement on the stream cipher Salsa, described at
 * http://cr.yp.to/papers.html#chacha
 */
#include <string.h>
#include <stdio.h>
#ifndef CHACHA_RNDS
#define CHACHA_RNDS 20    /* 8 (high speed), 20 (conservative), 12 (middle) */
#endif

/* Architecture-neutral way to specify 16-byte vector of ints              */
typedef unsigned vec __attribute__ ((vector_size (16)));

/* This implementation is designed for Neon, SSE and AltiVec machines. The
 * following specify how to do certain vector operations efficiently on
 * each architecture, using intrinsics.
 * This implementation supports parallel processing of multiple blocks,
 * including potentially using general-purpose registers.
 */
#if __ARM_NEON__
#include <arm_neon.h>
#define GPR_TOO   1
#define VBPI      2
#define ONE       (vec)vsetq_lane_u32(1,vdupq_n_u32(0),0)
#define NONCE(p)  (vec)vcombine_u32(vdup_n_u32(0),vcreate_u32(*(uint64_t *)p))
#define ROTV1(x)  (vec)vextq_u32((uint32x4_t)x,(uint32x4_t)x,1)
#define ROTV2(x)  (vec)vextq_u32((uint32x4_t)x,(uint32x4_t)x,2)
#define ROTV3(x)  (vec)vextq_u32((uint32x4_t)x,(uint32x4_t)x,3)
#define ROTW16(x) (vec)vrev32q_u16((uint16x8_t)x)
#if __clang__
#define ROTW7(x)  (x << ((vec){ 7, 7, 7, 7})) ^ (x >> ((vec){25,25,25,25}))
#define ROTW8(x)  (x << ((vec){ 8, 8, 8, 8})) ^ (x >> ((vec){24,24,24,24}))
#define ROTW12(x) (x << ((vec){12,12,12,12})) ^ (x >> ((vec){20,20,20,20}))
#else
#define ROTW7(x)  (vec)vsriq_n_u32(vshlq_n_u32((uint32x4_t)x,7),(uint32x4_t)x,25)
#define ROTW8(x)  (vec)vsriq_n_u32(vshlq_n_u32((uint32x4_t)x,8),(uint32x4_t)x,24)
#define ROTW12(x) (vec)vsriq_n_u32(vshlq_n_u32((uint32x4_t)x,12),(uint32x4_t)x,20)
#endif
#elif __ALTIVEC__
#include <altivec.h>
#define GPR_TOO    1
#define VBPI       3
#define ONE        ((vec){1,0,0,0})
#define NONCE(p)   vec_sro(*(vec *)p, (vector char)(vec){0,0,0,8*8})
#define REVW_BE(x) __builtin_bswap32(x)
#define REVV_BE(x) vec_perm(x,x,(vector char){3,2,1,0,7,6,5,4,11,10,9,8,15,14,13,12})
#define ROTV1(x)   vec_perm(x,x,(vector char){4,5,6,7,8,9,10,11,12,13,14,15,0,1,2,3})
#define ROTV2(x)   vec_perm(x,x,(vector char){8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7})
#define ROTV3(x)   vec_perm(x,x,(vector char){12,13,14,15,0,1,2,3,4,5,6,7,8,9,10,11})
#define ROTW7(x)   vec_rl(x,vec_splat_u32(7))
#define ROTW8(x)   vec_rl(x,vec_splat_u32(8))
#define ROTW12(x)  vec_rl(x,vec_splat_u32(12))
#define ROTW16(x)  vec_rl(x,vec_splat_u32(-16)) /* trick to get 16 */
#elif __SSE2__
#include <emmintrin.h>
#define GPR_TOO   0
#if __clang__
#define VBPI      4
#else
#define VBPI      3
#endif
#define ONE       (vec)_mm_set_epi32(0,0,0,1)
#define ROTV1(x)  (vec)_mm_shuffle_epi32((__m128i)x,_MM_SHUFFLE(0,3,2,1))
#define ROTV2(x)  (vec)_mm_shuffle_epi32((__m128i)x,_MM_SHUFFLE(1,0,3,2))
#define ROTV3(x)  (vec)_mm_shuffle_epi32((__m128i)x,_MM_SHUFFLE(2,1,0,3))
#define ROTW7(x)  (vec)(_mm_slli_epi32((__m128i)x, 7) ^ _mm_srli_epi32((__m128i)x,25))
#define ROTW12(x) (vec)(_mm_slli_epi32((__m128i)x,12) ^ _mm_srli_epi32((__m128i)x,20))
#if __SSSE3__
#include <tmmintrin.h>
#define ROTW8(x)  (vec)_mm_shuffle_epi8((__m128i)x,_mm_set_epi8(14,13,12,15,10,9,8,11,6,5,4,7,2,1,0,3))
#define ROTW16(x) (vec)_mm_shuffle_epi8((__m128i)x,_mm_set_epi8(13,12,15,14,9,8,11,10,5,4,7,6,1,0,3,2))
#else
#define ROTW8(x)  (vec)(_mm_slli_epi32((__m128i)x, 8) ^ _mm_srli_epi32((__m128i)x,24))
#define ROTW16(x) (vec)(_mm_slli_epi32((__m128i)x,16) ^ _mm_srli_epi32((__m128i)x,16))
#endif
#else
#error -- Implementation supports only machines with neon, altivec or SSE2
#endif

#ifndef REVV_BE
#define REVV_BE(x)  (x)
#endif

#ifndef REVW_BE
#define REVW_BE(x)  (x)
#endif

#define BPI      (VBPI + GPR_TOO)  /* Blocks computed per loop iteration   */

static inline void dqround_vectors(vec* v) {
  vec a = v[0];
  vec b = v[1];
  vec c = v[2];
  vec d = v[3];
    a += b; d ^= a; d = ROTW16(d);              
    c += d; b ^= c; b = ROTW12(b);              
    a += b; d ^= a; d = ROTW8(d);               
    c += d; b ^= c; b = ROTW7(b);               
    b = ROTV1(b); c = ROTV2(c);  d = ROTV3(d);  
    a += b; d ^= a; d = ROTW16(d);              
    c += d; b ^= c; b = ROTW12(b);              
    a += b; d ^= a; d = ROTW8(d);               
    c += d; b ^= c; b = ROTW7(b);               
    b = ROTV3(b); c = ROTV2(c); d = ROTV1(d);
  v[0] = a;
  v[1] = b;
  v[2] = c;
  v[3] = d;
}

#define DQROUND_VECTORS(a,b,c,d)                \
    a += b; d ^= a; d = ROTW16(d);              \
    c += d; b ^= c; b = ROTW12(b);              \
    a += b; d ^= a; d = ROTW8(d);               \
    c += d; b ^= c; b = ROTW7(b);               \
    b = ROTV1(b); c = ROTV2(c);  d = ROTV3(d);  \
    a += b; d ^= a; d = ROTW16(d);              \
    c += d; b ^= c; b = ROTW12(b);              \
    a += b; d ^= a; d = ROTW8(d);               \
    c += d; b ^= c; b = ROTW7(b);               \
    b = ROTV3(b); c = ROTV2(c); d = ROTV1(d);

static inline void qround_words(vec* v) {
  vec a = v[0];
  vec b = v[1];
  vec c = v[2];
  vec d = v[3];
  a = a+b; d ^= a; d = d<<16 | d>>16; 
  c = c+d; b ^= c; b = b<<12 | b>>20; 
  a = a+b; d ^= a; d = d<< 8 | d>>24; 
  c = c+d; b ^= c; b = b<< 7 | b>>25;
  v[0] = a;
  v[1] = b;
  v[2] = c;
  v[3] = d;
}

#define QROUND_WORDS(a,b,c,d) \
  a = a+b; d ^= a; d = d<<16 | d>>16; \
  c = c+d; b ^= c; b = b<<12 | b>>20; \
  a = a+b; d ^= a; d = d<< 8 | d>>24; \
  c = c+d; b ^= c; b = b<< 7 | b>>25;

#define WRITE_XOR(in, op, d, v0, v1, v2, v3)                   \
*(vec *)(op + d +  0) = *(vec *)(in + d +  0) ^ REVV_BE(v0);    \
*(vec *)(op + d +  4) = *(vec *)(in + d +  4) ^ REVV_BE(v1);    \
*(vec *)(op + d +  8) = *(vec *)(in + d +  8) ^ REVV_BE(v2);    \
*(vec *)(op + d + 12) = *(vec *)(in + d + 12) ^ REVV_BE(v3);

#define WRITE(op, d, v0, v1, v2, v3)                   \
*(vec *)(op + d +  0) = REVV_BE(v0);    \
*(vec *)(op + d +  4) = REVV_BE(v1);    \
*(vec *)(op + d +  8) = REVV_BE(v2);    \
*(vec *)(op + d + 12) = REVV_BE(v3);

int crypto_stream_xor_ic(
        unsigned char *out,
        const unsigned char *in,
        unsigned long long inlen,
        const unsigned char *n,
        const unsigned char *k,
	const unsigned ctr
)
/* Assumes all pointers are aligned properly for vector reads */
{
    unsigned iters, i, *op=(unsigned *)out, *ip=(unsigned *)in, *kp, *np;
    __attribute__ ((aligned (16))) unsigned key[8], nonce[3];
    __attribute__ ((aligned (16))) unsigned chacha_const[] =
                                {0x61707865,0x3320646E,0x79622D32,0x6B206574};
    #if ( __ARM_NEON__ || __SSE2__)
    kp = (unsigned *)k;
    np = (unsigned *)n;
    #else
    ((vec *)key)[0] = REVV_BE(((vec *)k)[0]);
    ((vec *)key)[1] = REVV_BE(((vec *)k)[1]);
    nonce[0] = REVW_BE(((unsigned *)n)[0]);
    nonce[1] = REVW_BE(((unsigned *)n)[1]);
    nonce[2] = REVW_BE(((unsigned *)n)[2]);
    kp = (unsigned *)key;
    np = (unsigned *)nonce;
    #endif
    vec s0 = *(vec *)chacha_const;
    vec s1 = ((vec *)kp)[0];
    vec s2 = ((vec *)kp)[1];

    vec s3 = (vec) {ctr,nonce[0],nonce[1],nonce[2]};
    for (iters = 0; iters < inlen/(BPI*64); iters++) {
        vec v0,v1,v2,v3,v4,v5,v6,v7;
        v4 = v0 = s0; v5 = v1 = s1; v6 = v2 = s2; v3 = s3;
        v7 = v3 + ONE;
        #if VBPI > 2
        vec v8,v9,v10,v11;
        v8 = v4; v9 = v5; v10 = v6;
        v11 =  v7 + ONE;
        #endif
        #if VBPI > 3
        vec v12,v13,v14,v15;
        v12 = v8; v13 = v9; v14 = v10;
        v15 = v11 + ONE;
        #endif
        #if GPR_TOO
        register unsigned x0, x1, x2, x3, x4, x5, x6, x7, x8,
                          x9, x10, x11, x12, x13, x14, x15;
        x0 = chacha_const[0]; x1 = chacha_const[1];
        x2 = chacha_const[2]; x3 = chacha_const[3];
        x4 = kp[0]; x5 = kp[1]; x6  = kp[2]; x7  = kp[3];
        x8 = kp[4]; x9 = kp[5]; x10 = kp[6]; x11 = kp[7];
        x12 = BPI*iters+(BPI-1); x13 = 0; x14 = np[0]; x15 = np[1];
        #endif
	vec v[4];
        for (i = CHACHA_RNDS/2; i; i--) {
	  v[0] = v0; v[1] = v1; v[2] = v2; v[3] = v3;
	  dqround_vectors(v);
          v0 = v[0]; v1 = v[1]; v2 = v[2]; v2 = v[3];
      
	  v[0] = v4; v[1] = v5; v[2] = v6; v[3] = v7;
	  dqround_vectors(v);
          v4 = v[0]; v5 = v[1]; v6 = v[2]; v7 = v[3];
            #if VBPI > 2
	  v[0] = v8; v[1] = v9; v[2] = v10; v[3] = v11;
	  dqround_vectors(v);
          v8 = v[0]; v9 = v[1]; v10 = v[2]; v11 = v[3];
            #endif
            #if VBPI > 3
	  v[0] = v12; v[1] = v13; v[2] = v14; v[3] = v15;
	  dqround_vectors(v);
          v12 = v[0]; v13 = v[1]; v14 = v[2]; v15 = v[3];
            #endif
            #if GPR_TOO
	      printf("here");
            QROUND_WORDS( x0, x4, x8,x12)
            QROUND_WORDS( x1, x5, x9,x13)
            QROUND_WORDS( x2, x6,x10,x14)
            QROUND_WORDS( x3, x7,x11,x15)
            QROUND_WORDS( x0, x5,x10,x15)
            QROUND_WORDS( x1, x6,x11,x12)
            QROUND_WORDS( x2, x7, x8,x13)
            QROUND_WORDS( x3, x4, x9,x14)
            #endif
        }
        WRITE_XOR(ip, op, 0, v0+s0, v1+s1, v2+s2, v3+s3)
        s3 += ONE;
        WRITE_XOR(ip, op, 16, v4+s0, v5+s1, v6+s2, v7+s3)
        s3 += ONE;
        #if VBPI > 2
        WRITE_XOR(ip, op, 32, v8+s0, v9+s1, v10+s2, v11+s3)
        s3 += ONE;
        #endif
        #if VBPI > 3
        WRITE_XOR(ip, op, 48, v12+s0, v13+s1, v14+s2, v15+s3)
        s3 += ONE;
        #endif
        ip += VBPI*16;
        op += VBPI*16;
        #if GPR_TOO
        op[0]  = REVW_BE(REVW_BE(ip[0])  ^ (x0  + chacha_const[0]));
        op[1]  = REVW_BE(REVW_BE(ip[1])  ^ (x1  + chacha_const[1]));
        op[2]  = REVW_BE(REVW_BE(ip[2])  ^ (x2  + chacha_const[2]));
        op[3]  = REVW_BE(REVW_BE(ip[3])  ^ (x3  + chacha_const[3]));
        op[4]  = REVW_BE(REVW_BE(ip[4])  ^ (x4  + kp[0]));
        op[5]  = REVW_BE(REVW_BE(ip[5])  ^ (x5  + kp[1]));
        op[6]  = REVW_BE(REVW_BE(ip[6])  ^ (x6  + kp[2]));
        op[7]  = REVW_BE(REVW_BE(ip[7])  ^ (x7  + kp[3]));
        op[8]  = REVW_BE(REVW_BE(ip[8])  ^ (x8  + kp[4]));
        op[9]  = REVW_BE(REVW_BE(ip[9])  ^ (x9  + kp[5]));
        op[10] = REVW_BE(REVW_BE(ip[10]) ^ (x10 + kp[6]));
        op[11] = REVW_BE(REVW_BE(ip[11]) ^ (x11 + kp[7]));
        op[12] = REVW_BE(REVW_BE(ip[12]) ^ (x12 + BPI*iters+(BPI-1)));
        op[13] = REVW_BE(REVW_BE(ip[13]) ^ (x13));
        op[14] = REVW_BE(REVW_BE(ip[14]) ^ (x14 + np[0]));
        op[15] = REVW_BE(REVW_BE(ip[15]) ^ (x15 + np[1]));
        s3 += ONE;
        ip += 16;
        op += 16;
        #endif
    }
    vec v[4];
    for (iters = inlen%(BPI*64)/64; iters != 0; iters--) {
        vec v0 = s0, v1 = s1, v2 = s2, v3 = s3;
        for (i = CHACHA_RNDS/2; i; i--) {
	  v[0] = v0; v[1] = v1; v[2] = v2; v[3] = v3;
	  dqround_vectors(v);
          v0 = v[0]; v1 = v[1]; v2 = v[2]; v2 = v[3];
        }
        WRITE_XOR(ip, op, 0, v0+s0, v1+s1, v2+s2, v3+s3)
        s3 += ONE;
        ip += 16;
        op += 16;
    }
    inlen = inlen % 64;
    if (inlen) {
        __attribute__ ((aligned (16))) char buf[16];
        vec tail;
        vec v0,v1,v2,v3;
        v0 = s0; v1 = s1; v2 = s2; v3 = s3;
        for (i = CHACHA_RNDS/2; i; i--) {
	  v[0] = v0; v[1] = v1; v[2] = v2; v[3] = v3;
	  dqround_vectors(v);
          v0 = v[0]; v1 = v[1]; v2 = v[2]; v2 = v[3];
        }
        if (inlen >= 32) {
            *(vec *)(op +   0) = *(vec *)(ip +   0) ^ REVV_BE(v0 + s0);
            *(vec *)(op +  4) = *(vec *)(ip + 4) ^ REVV_BE(v1 + s1);
            if (inlen >= 48) {
                *(vec *)(op +  8) = *(vec *)(ip +  8) ^ REVV_BE(v2 + s2);
                tail = REVV_BE(v3 + s3); op += 12; ip += 12; inlen -= 48;
            } else { tail = REVV_BE(v2 + s2); op += 8; ip += 8; inlen -= 32; }
        } else if (inlen >= 16) {
                *(vec *)(op +   0) = *(vec *)(ip +   0) ^ REVV_BE(v0 + s0);
                tail = REVV_BE(v1 + s1); op += 4; ip += 4; inlen -= 16; 
        } else tail = REVV_BE(v0 + s0); 
        memcpy(buf,ip,inlen);
        *(vec *)buf = tail ^ *(vec *)buf;
        memcpy(op,buf,inlen);
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
