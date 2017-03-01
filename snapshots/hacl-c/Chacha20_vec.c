/* Code shamelessly copied from Krovetz's implementation */
#include "Chacha20_vec.h"
#include "vec128.h"

static inline vec rotate_vec1 (vec v){ return RORV(v,1); }
static inline vec rotate_vec2 (vec v){ return RORV(v,2); }
static inline vec rotate_vec3 (vec v){ return RORV(v,3); }

static inline vec vec_rotate_left(vec v, unsigned int n) {
  return ((vec)((v << n) ^ (v >> (32-n))));
}

static inline void dqround_vectors(vec* v) {
  vec a = v[0];
  vec b = v[1];
  vec c = v[2];
  vec d = v[3];
  a += b; d ^= a; d = vec_rotate_left(d,16);              
  c += d; b ^= c; b = vec_rotate_left(b,12);              
  a += b; d ^= a; d = vec_rotate_left(d,8);               
  c += d; b ^= c; b = vec_rotate_left(b,7);
  b = rotate_vec1(b); c = rotate_vec2(c);  d = rotate_vec3(d);  
  a += b; d ^= a; d = vec_rotate_left(d,16);
  c += d; b ^= c; b = vec_rotate_left(b,12);
  a += b; d ^= a; d = vec_rotate_left(d,8);               
  c += d; b ^= c; b = vec_rotate_left(b,7);               
  b = rotate_vec3(b); c = rotate_vec2(c); d = rotate_vec1(d);
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
/* This function is the only one that depends on the vector size */
static inline void write_xor(unsigned* in, unsigned* out, vec* v) {
#if defined(VEC256)
    vec v0 = (vec){in[0],in[1],in[2],in[3],in[16],in[17],in[18],in[19]};
    vec v1 = (vec){in[4],in[5],in[6],in[7],in[20],in[21],in[22],in[23]};
    vec v2 = (vec){in[8],in[9],in[10],in[11],in[24],in[25],in[26],in[27]};
    vec v3 = (vec){in[12],in[13],in[14],in[15],in[28],in[29],in[30],in[31]};
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
    out[16] = v0[4];
    out[17] = v0[5];
    out[18] = v0[6];
    out[19] = v0[7];
    out[20] = v1[4];
    out[21] = v1[5];
    out[22] = v1[6];
    out[23] = v1[7];
    out[24] = v2[4];
    out[25] = v2[5];
    out[26] = v2[6];
    out[27] = v2[7];
    out[28] = v3[4];
    out[29] = v3[5];
    out[30] = v3[6];
    out[31] = v3[7];
#elif defined(VEC128)
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
#else
    printf("only vec_size 16/32 supported\n");
    exit(1);
#endif
}

static inline void chacha20_block(unsigned char* out, const unsigned char* in, vec* st) {
  unsigned* op = (unsigned*) out;
  unsigned* ip = (unsigned*) in;
  vec v[4];
  chacha20_core(v,st);
  write_xor(ip, op, v);
  st[3] += ONE;
}

static inline void chacha20_block3(unsigned char* out, const unsigned char* in, vec* st) {
  unsigned* op = (unsigned*) out;
  unsigned* ip = (unsigned*) in;
  vec v0[4],v1[4],v2[4];
  chacha20_core3(v0,v1,v2,st);
  write_xor(ip, op, v0);
  write_xor(ip+vec_size, op+vec_size, v1);
  write_xor(ip+(2 * vec_size), op+(2* vec_size), v2);
}

int crypto_stream_xor(
        unsigned char *out,
        const unsigned char *in,
        unsigned long long inlen,
        const unsigned char *n,
        const unsigned char *k
)
{
  /* Assumes all pointers are aligned properly for vector reads */
    unsigned * kp = (unsigned *)k;
    unsigned * np = (unsigned *)n;
    vec st[4];
    st[0] = (vec) {0x61707865,0x3320646E,0x79622D32,0x6B206574};
    st[1] = (vec) {kp[0], kp[1], kp[2], kp[3]};
    st[1] = (vec) {kp[4], kp[5], kp[6], kp[7]};
    st[3] = (vec) {1,     np[0], np[1], np[2]};
    int blocks = vec_size / 16;
    int iters;
    for (iters = 0; iters < inlen/(3*blocks*64); iters++) {
      chacha20_block3(out,in,st);
      in += 3*blocks*64;
      out += 3*blocks*64;
    }
    inlen = inlen % (3*blocks*64);
    for (iters = inlen/(blocks*64); iters != 0; iters--) {
      chacha20_block(out,in,st);
      in += blocks*64;
      out+= blocks*64;
    }
    inlen = inlen % (blocks*64);
    if (inlen) {
        __attribute__ ((aligned (16))) char buf[blocks*64];
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
