/* Code shamelessly copied from Krovetz's implementation */
#include "Chacha20_vec.h"
#include "Chacha20_state.h"

static inline void dqround_vectors(chacha20_state v) {
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

static inline void chacha20_core(chacha20_state v, chacha20_state s) {
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
static inline void chacha20_core3(chacha20_state v0, chacha20_state v1, chacha20_state v2, chacha20_state s) {
  vec one = one_128_le();
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
  v2[0] = vec_add(v2[0],s[0]);
  v2[1] = vec_add(v2[1],s[1]);
  v2[2] = vec_add(v2[2],s[2]);
  v2[3] = vec_add(v2[3],s[3]);
  s[3]  = vec_add(s[3],one);
}

static inline void chacha20_core2(chacha20_state v0, chacha20_state v1, chacha20_state s) {
  vec one = one_128_le();
  v0[0] = v1[0] = s[0];
  v0[1] = v1[1] = s[1];
  v0[2] = v1[2] = s[2];
  v0[3] = v1[3] = s[3];
  for (int i = 0; i < 10; i++) {
    dqround_vectors(v0);
    dqround_vectors(v1);
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
}

/* this ones costs 0.5 cycle/byte, try to optimize */
/* This function and init are the only ones that depends on the vector size */
static inline void write_xor(const unsigned char* in, unsigned char* out, chacha20_state v) {
  vec k[4];
  chacha20_state_to_key(k,v);
  vec i0 = vec_load(in);
  vec i1 = vec_load(in+vec_size);
  vec i2 = vec_load(in+(2*vec_size));
  vec i3 = vec_load(in+(3*vec_size));
  k[0] = vec_xor(k[0],i0);
  k[1] = vec_xor(k[1],i1);
  k[2] = vec_xor(k[2],i2);
  k[3] = vec_xor(k[3],i3);
  vec_store(out,k[0]);
  vec_store(out+vec_size,k[1]);
  vec_store(out+(2*vec_size),k[2]);
  vec_store(out+(3*vec_size),k[3]);
}

static inline void chacha20_init(chacha20_state st, const unsigned char* k, const unsigned char* n, unsigned int ctr) {
  chacha20_state_init(st,k,n,ctr);
}

static inline void chacha20_block(unsigned char* out, const unsigned char* in, chacha20_state st) {
  vec v[4];
  chacha20_core(v,st);
  write_xor(in, out, v);
  vec one = one_128_le();
  st[3] = vec_add(st[3],one);
}

static inline void chacha20_block3(unsigned char* out, const unsigned char* in, chacha20_state st) {
  vec v0[4],v1[4],v2[4];
  int blocks = vec_size / 16;
  chacha20_core3(v0,v1,v2,st);
  write_xor(in, out, v0);
  write_xor(in+(64 * blocks), out+(64 * blocks), v1);
  write_xor(in+(128 * blocks), out+(128 * blocks), v2);
}

static inline void chacha20_block2(unsigned char* out, const unsigned char* in, chacha20_state st) {
  vec v0[4],v1[4];
  int blocks = vec_size / 16;
  chacha20_core2(v0,v1,st);
  write_xor(in, out, v0);
  write_xor(in+(64 * blocks), out+(64 * blocks), v1);
}

int chacha20_init_block(unsigned char* out, chacha20_state st, const unsigned char* k, const unsigned char* n, unsigned int ctr) {
  chacha20_state_init(st,k,n,ctr);
  vec v[4];
  chacha20_core(v,st);
  vec_store(out,v[0]);
  vec_store(out+vec_size,v[1]);
  vec_store(out+(2*vec_size),v[2]);
  vec_store(out+(3*vec_size),v[3]);
  vec one = one_128_le();
  st[3] = vec_add(st[3],one);
}

int chacha20_continue(        
	unsigned char *out,
        const unsigned char *in,
        unsigned long long inlen,
        chacha20_state st) {
    int blocks = vec_size / 16;
    int iters;
    /* 
    for (iters = 0; iters < inlen/(3*blocks*64); iters++) {
      chacha20_block3(out,in,st);
      in += 3*blocks*64;
      out += 3*blocks*64;
    }
    inlen = inlen % (3*blocks*64);
    */
    for (iters = 0; iters < inlen/(2*blocks*64); iters++) {
      chacha20_block2(out,in,st);
      in += 2*blocks*64;
      out += 2*blocks*64;
    }
    inlen = inlen % (2*blocks*64);
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
