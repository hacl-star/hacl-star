/* Code shamelessly copied from Krovetz's implementation */
#include "Chacha20_vec.h"
#include "vec128.h"

#ifdef VEC256
const vec ONE = {1,0,0,0,1,0,0,0};
#else
const vec ONE = {1,0,0,0};
#endif 

static inline void dqround_vectors(vec* v) {
  vec a = v[0];
  vec b = v[1];
  vec c = v[2];
  vec d = v[3];
  a = vec_add(a,b); d = vec_xor(d,a); d = vec_rotate_left(d,16);              
  c = vec_add(c,d); b = vec_xor(b,c); b = vec_rotate_left(b,12);              
  a = vec_add(a,b); d = vec_xor(d,a); d = vec_rotate_left(d,8);               
  c = vec_add(c,d); b = vec_xor(b,c); b = vec_rotate_left(b,7);
  b = vec_shuffle_right(b,1); c = vec_shuffle_right(c,2);  d = vec_shuffle_right(d,3);  
  a = vec_add(a,b); d = vec_xor(d,a); d = vec_rotate_left(d,16);              
  c = vec_add(c,d); b = vec_xor(b,c); b = vec_rotate_left(b,12);              
  a = vec_add(a,b); d = vec_xor(d,a); d = vec_rotate_left(d,8);               
  c = vec_add(c,d); b = vec_xor(b,c); b = vec_rotate_left(b,7);
  b = vec_shuffle_right(b,3); c = vec_shuffle_right(c,2); d = vec_shuffle_right(d,1);
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
  v[0] = vec_add(v[0],s[0]);
  v[1] = vec_add(v[1],s[1]);
  v[2] = vec_add(v[2],s[2]);
  v[3] = vec_add(v[3],s[3]);
}

/* This following function works much better with the 3 dqrounds in a row.
   2x slower if I split them up */
static inline void chacha20_core3(vec* v0, vec*v1, vec* v2, vec* s) {
  vec one = ONE;
  v0[0] = v1[0] = v2[0] = s[0];
  v0[1] = v1[1] = v2[1] = s[1];
  v0[2] = v1[2] = v2[2] = s[2];
  v0[3] = v1[3] = v2[3] = s[3];
  for (int i = 0; i < 10; i++) {
    dqround_vectors(v0);
    dqround_vectors(v1);
    dqround_vectors(v2);
  }
  v0[0] = vec_add(v0[0],s[0]);
  v0[1] = vec_add(v0[1],s[1]);
  v0[2] = vec_add(v0[2],s[2]);
  v0[3] = vec_add(v0[3],s[3]);
  s[3]  = vec_add(s[3],one);
  v1[0] = vec_add(v1[0],s[0]);
  v1[1] = vec_add(v1[1],s[1]);
  v1[2] = vec_add(v1[2],s[2]);
  v1[3] = vec_add(v1[3],s[3]);
  s[3]  = vec_add(s[3],one);
  v2[0] = v2[0] + s[0];
  v2[1] = v2[1] + s[1];
  v2[2] = v2[2] + s[2];
  v2[3] = v2[3] + s[3];
  s[3]  = vec_add(s[3],one);
}

/* this ones costs 0.5 cycle/byte, try to optimize */
/* This function and init are the only ones that depends on the vector size */
static inline void write_xor(const unsigned char* in, unsigned char* out, vec* v) {
#if defined(VEC256)
  vec v0 = vec256_choose_128(v[0], v[1], 0, 2);
  vec v1 = vec256_choose_128(v[2], v[3], 0, 2);
  vec v2 = vec256_choose_128(v[0], v[1], 1, 3);
  vec v3 = vec256_choose_128(v[2], v[3], 1, 3);
#elif  defined(VEC128)
  vec v0 = v[0];
  vec v1 = v[1];
  vec v2 = v[2];
  vec v3 = v[3];
#else
    printf("only vec_size 16/32 supported\n");
    exit(1);
#endif
  vec i0 = vec_load(in);
  vec i1 = vec_load(in+vec_size);
  vec i2 = vec_load(in+(2*vec_size));
  vec i3 = vec_load(in+(3*vec_size));
  v0 = vec_xor(v0,i0);
  v1 = vec_xor(v1,i1);
  v2 = vec_xor(v2,i2);
  v3 = vec_xor(v3,i3);
  vec_store(out,v0);
  vec_store(out+vec_size,v1);
  vec_store(out+(2*vec_size),v2);
  vec_store(out+(3*vec_size),v3);
}

static inline void chacha20_init(vec* st, const unsigned char* k, const unsigned char* n, unsigned int ctr) {
  unsigned * kp = (unsigned *)k;
  unsigned * np = (unsigned *)n;
#if defined(VEC256)
  st[0] = (vec) {0x61707865,0x3320646E,0x79622D32,0x6B206574,0x61707865,0x3320646E,0x79622D32,0x6B206574}; 
  st[1] = (vec) {kp[0], kp[1], kp[2], kp[3],kp[0], kp[1], kp[2], kp[3]};
  st[2] = (vec) {kp[4], kp[5], kp[6], kp[7],kp[4], kp[5], kp[6], kp[7]};
  st[3] = (vec) {ctr,   np[0], np[1], np[2],ctr+1, np[0], np[1], np[2]};
#elif defined(VEC128)
  st[0] = (vec) {0x61707865,0x3320646E,0x79622D32,0x6B206574};
  st[1] = (vec) {kp[0], kp[1], kp[2], kp[3]};
  st[2] = (vec) {kp[4], kp[5], kp[6], kp[7]};
  st[3] = (vec) {ctr,   np[0], np[1], np[2]};
#else
    printf("only vec_size 128/256 supported\n");
    exit(1);
#endif
}

static inline void chacha20_block(unsigned char* out, const unsigned char* in, vec* st) {
  vec one = ONE;
  vec v[4];
  chacha20_core(v,st);
  write_xor(in, out, v);
  st[3] = st[3] + one;
}

static inline void chacha20_block3(unsigned char* out, const unsigned char* in, vec* st) {
  vec v0[4],v1[4],v2[4];
  int blocks = vec_size / 16;
  chacha20_core3(v0,v1,v2,st);
  write_xor(in, out, v0);
  write_xor(in+(64 * blocks), out+(64 * blocks), v1);
  write_xor(in+(128 * blocks), out+(128 * blocks), v2);
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
  /* Assumes all pointers are aligned properly for vector reads */
    vec st[4];
    chacha20_init(st,k,n,ctr);
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

int crypto_stream_xor(
        unsigned char *out,
        const unsigned char *in,
        unsigned long long inlen,
        const unsigned char *n,
        const unsigned char *k
)
{
  return crypto_stream_xor_ic(out,in,inlen,n,k,0);
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
