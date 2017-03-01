/* Code shamelessly copied from Krovetz's implementation */
#include "Chacha20_vec.h"

#define CHACHA_RNDS 20

typedef unsigned vec __attribute__ ((vector_size (16)));


#define GPR_TOO 0
#define VBPI 3
#define ONE (vec)_mm_set_epi32(1,0,0,0)
#define NONCE(p) (vec)_mm_slli_si128(_mm_loadl_epi64((__m128i *)(p)),8)

#define RORV(x,n) (vec)_mm_shuffle_epi32((__m128i)x,_MM_SHUFFLE((3+n)%4,(2+n)%4,(1+n)%4,n%4))
#define ROTV1(x)  RORV(x,1)
#define ROTV2(x)  RORV(x,2)
#define ROTV3(x)  RORV(x,3)

#define ROTW7(x) (vec)((x << 7) ^ (x >> 25))
#define ROTW12(x) (vec)((x << 12) ^ (x >> 20))
#define ROTW8(x) (vec)((x << 8) ^ (x >> 24))
#define ROTW16(x) (vec)((x << 16) ^ (x >> 16))

#define BPI (VBPI + GPR_TOO)

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

static inline void chacha20_core(vec* v, vec* s) {
  v[0] = s[0];
  v[1] = s[1];
  v[2] = s[2];
  v[3] = s[3];
  for (int i = 0; i < 10; i++)  dqround_vectors(v);
  v[0] = v[0] + s[0];
  v[1] = v[1] + s[1];
  v[2] = v[2] + s[2];
  v[3] = v[3] + s[3];
}

/* This following function works much better with the 3 dqrounds in a row.
   2x slower if I split them up */
static inline void chacha20_core3(vec* v0, vec*v1, vec* v2, vec* s) {
  v0[0] = v1[0] = v2[0] = s[0];
  v0[1] = v1[1] = v2[1] = s[1];
  v0[2] = v1[2] = v2[2] = s[2];
  v0[3] = v1[3] = v2[3] = s[3];
  for (int i = 0; i < 10; i++) {
    dqround_vectors(v0);
    dqround_vectors(v1);
    dqround_vectors(v2);
  }
  v0[0] = v0[0] + s[0];
  v0[1] = v0[1] + s[1];
  v0[2] = v0[2] + s[2];
  v0[3] = v0[3] + s[3];
  s[3] = s[3] + ONE;
  v1[0] = v1[0] + s[0];
  v1[1] = v1[1] + s[1];
  v1[2] = v1[2] + s[2];
  v1[3] = v1[3] + s[3];
  s[3] = s[3] + ONE;
  v2[0] = v2[0] + s[0];
  v2[1] = v2[1] + s[1];
  v2[2] = v2[2] + s[2];
  v2[3] = v2[3] + s[3];
  s[3] = s[3] + ONE;
}

/* this ones costs 0.5 cycle/byte, try to optimize */
static inline void write_xor(unsigned* in, unsigned* out, vec* v) {
  vec v0 = (vec){in[0],in[1],in[2],in[3]};
  vec v1 = (vec){in[4],in[5],in[6],in[7]};
  vec v2 = (vec){in[8],in[9],in[10],in[11]};
  vec v3 = (vec){in[12],in[13],in[14],in[15]};
  v0 = v0 ^ v[0];
  v1 = v1 ^ v[1];
  v2 = v2 ^ v[2];
  v3 = v3 ^ v[3];
  out[0] = v0[0];
  out[1] = v0[1];
  out[2] = v0[2];
  out[3] = v0[3];
  out[4] = v1[0];
  out[5] = v1[1];
  out[6] = v1[2];
  out[7] = v1[3];
  out[8] = v2[0];
  out[9] = v2[1];
  out[10] = v2[2];
  out[11] = v2[3];
  out[12] = v3[0];
  out[13] = v3[1];
  out[14] = v3[2];
  out[15] = v3[3];
}

static inline void chacha20_block(char* out, const char* in, vec* st) {
  unsigned* op = (unsigned*) out;
  unsigned* ip = (unsigned*) in;
  vec v[4];
  chacha20_core(v,st);
  write_xor(ip, op, v);
  st[3] += ONE;
}

static inline void chacha20_block3(char* out, const char* in, vec* st) {
  unsigned* op = (unsigned*) out;
  unsigned* ip = (unsigned*) in;
  vec v0[4],v1[4],v2[4];
  chacha20_core3(v0,v1,v2,st);
  write_xor(ip, op, v0);
  write_xor(ip+16, op+16, v1);
  write_xor(ip+32, op+32, v2);
}

int crypto_stream_xor(
        unsigned char *out,
        const unsigned char *in,
        unsigned long long inlen,
        const unsigned char *n,
        const unsigned char *k
)
/* Assumes all pointers are aligned properly for vector reads */
{
    unsigned * kp = (unsigned *)k;
    unsigned * np = (unsigned *)n;
    vec st[4];
    st[0] = (vec) {0x61707865,0x3320646E,0x79622D32,0x6B206574};
    st[1] = (vec) {kp[0], kp[1], kp[2], kp[3]};
    st[1] = (vec) {kp[4], kp[5], kp[6], kp[7]};
    st[3] = (vec) {1,     np[0], np[1], np[2]};
    int iters;
    for (iters = 0; iters < inlen/(3*64); iters++) {
      chacha20_block3(out,in,st);
      in += 3*64;
      out += 3*64;
    }
    for (iters = inlen%(3*64)/64; iters != 0; iters--) {
      chacha20_block(out,in,st);
      in += 64;
      out+= 64;
    }
    inlen = inlen % 64;
    if (inlen) {
        __attribute__ ((aligned (16))) char buf[64];
        memcpy(buf,in,inlen);
	chacha20_block(buf,buf,st);
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
