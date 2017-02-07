#include "Salsa20.h"

inline static uint32_t Hacl_Symmetric_Salsa20_rol32(uint32_t a, uint32_t s)
{
  return a << s | a >> (uint32_t )32 - s;
}

inline static uint32_t Hacl_Symmetric_Salsa20_load32_le(const uint8_t *k)
{
  return load32_le(k);
}

inline static void Hacl_Symmetric_Salsa20_store32_le(uint8_t *k, uint32_t x)
{
  store32_le(k, x);
  return;
}

#include <immintrin.h>
#include <ammintrin.h>

typedef unsigned int v32x4 __attribute__((vector_size (16)));

static const v32x4 v7 = {7,7,7,7};
static const v32x4 v9 = {9,9,9,9};
static const v32x4 v13 = {13,13,13,13};
static const v32x4 v18 = {18,18,18,18};

static const v32x4 v25 = {25,25,25,25};
static const v32x4 v23 = {23,23,23,23};
static const v32x4 v19 = {19,19,19,19};
static const v32x4 v14 = {14,14,14,14};

#define XOR32x4(a,b)	(v32x4)_mm_xor_si128((__m128i)a, (__m128i)b)
#define ADD32x4(a,b)	(v32x4)_mm_add_epi32((__m128i)a, (__m128i)b)
#define ROL32x4(a,b)	XOR32x4(_mm_slli_epi32((__m128i)a, (int)b),_mm_srli_epi32((__m128i)a, (int)(32-b)))
#define PERM1(a)        (v32x4)_mm_shuffle_epi32((__m128i)a,_MM_SHUFFLE(1,2,3,0))
#define PERM2(a)        (v32x4)_mm_shuffle_epi32((__m128i)a,_MM_SHUFFLE(2,3,0,1))
#define PERM3(a)        (v32x4)_mm_shuffle_epi32((__m128i)a,_MM_SHUFFLE(3,0,1,2))
#define LOAD32x4(m)	(v32x4)_mm_loadu_si128((__m128i*)(m))
#define STORE32x4(m,r)	_mm_storeu_si128((__m128i*)(m), (__m128i) (r))

force_inline inline static void
Hacl_Symmetric_Salsa20_salsa20_double_round(v32x4* v)
{
  v32x4 y0 = v[0];
  v32x4 y1 = v[1];
  v32x4 y2 = v[2];
  v32x4 y3 = v[3];

  y1 = XOR32x4(y1,ROL32x4(ADD32x4(y0,y3),7));
  y2 = XOR32x4(y2,ROL32x4(ADD32x4(y1,y0),9));
  y3 = XOR32x4(y3,ROL32x4(ADD32x4(y2,y1),13));
  y0 = XOR32x4(y0,ROL32x4(ADD32x4(y3,y2),18));

  y1 = PERM1(y3);
  y2 = PERM2(y2);
  y3 = PERM3(y1);

  y1 = XOR32x4(y1,ROL32x4(ADD32x4(y0,y3),7));
  y2 = XOR32x4(y2,ROL32x4(ADD32x4(y1,y0),9));
  y3 = XOR32x4(y3,ROL32x4(ADD32x4(y2,y1),13));
  y0 = XOR32x4(y0,ROL32x4(ADD32x4(y3,y2),18));

  y1 = PERM1(y3);
  y2 = PERM2(y2);
  y3 = PERM3(y1);

  v[0] = y0;
  v[1] = y1;
  v[2] = y2;
  v[3] = y3;
}

force_inline  inline static void Hacl_Symmetric_Salsa20_salsa20_double_round_10(v32x4 *v)
{
  Hacl_Symmetric_Salsa20_salsa20_double_round(v);
  Hacl_Symmetric_Salsa20_salsa20_double_round(v);
  Hacl_Symmetric_Salsa20_salsa20_double_round(v);
  Hacl_Symmetric_Salsa20_salsa20_double_round(v);
  Hacl_Symmetric_Salsa20_salsa20_double_round(v);
  Hacl_Symmetric_Salsa20_salsa20_double_round(v);
  Hacl_Symmetric_Salsa20_salsa20_double_round(v);
  Hacl_Symmetric_Salsa20_salsa20_double_round(v);
  Hacl_Symmetric_Salsa20_salsa20_double_round(v);
  Hacl_Symmetric_Salsa20_salsa20_double_round(v);
  return;
}

inline static void
Hacl_Symmetric_Salsa20_salsa20_init(v32x4 *v, const uint8_t *key, const uint8_t *n, uint64_t ic)
{
  uint32_t c1 = Hacl_Symmetric_Salsa20_load32_le(key);
  uint32_t c2 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )4);
  uint32_t c3 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )8);
  uint32_t c4 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )12);
  uint32_t c11 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )16);
  uint32_t c12 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )20);
  uint32_t c13 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )24);
  uint32_t c14 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )28);
  uint32_t c6 = Hacl_Symmetric_Salsa20_load32_le(n);
  uint32_t c7 = Hacl_Symmetric_Salsa20_load32_le(n + (uint32_t )4);
  uint32_t c8 = (uint32_t )ic;
  uint32_t c9 = (uint32_t )(ic >> (uint32_t )32);

  v32x4 v0 = (v32x4) {
    0x61707865,
    0x3320646e,
    0x79622d32,
    0x6b206574
  };  
  v32x4 v1 = (v32x4) {c4,c9,c14,c3};
  v32x4 v2 = (v32x4) {c8,c13,c2,c7};
  v32x4 v3 = (v32x4) {c12,c1,c6,c11};
  v[0] = v0;
  v[1] = v1;
  v[2] = v2;
  v[3] = v3;
}

inline static void
Hacl_Symmetric_Salsa20_salsa20_finish(uint8_t *block,v32x4 *v)
{
  block[0] = v[0][0];
  block[1] = v[3][1];
  block[2] = v[2][2];
  block[3] = v[1][3];
  block[4] = v[1][0];
  block[5] = v[0][1];
  block[6] = v[3][2];
  block[7] = v[2][3];
  block[8] = v[2][1];
  block[9] = v[1][1];
  block[10] = v[0][2];
  block[11] = v[3][3];
  block[12] = v[3][0];
  block[13] = v[2][1];
  block[14] = v[1][2];
  block[15] = v[0][3];
}

force_inline  inline static void Hacl_Symmetric_Salsa20_salsa20(v32x4 *output, const v32x4* v)
{
  v32x4 v0 = v[0];
  v32x4 v1 = v[1];
  v32x4 v2 = v[2];
  v32x4 v3 = v[3];
  output[0] = v0;
  output[1] = v1;
  output[2] = v2;
  output[3] = v3;
  Hacl_Symmetric_Salsa20_salsa20_double_round_10(output);
  v32x4 x0 = output[0];
  v32x4 x1 = output[1];
  v32x4 x2 = output[2];
  v32x4 x3 = output[3];
  x0 = ADD32x4(x0,v0);
  x1 = ADD32x4(x1,v1);
  x2 = ADD32x4(x2,v2);
  x3 = ADD32x4(x1,v3);
  output[0] = x0;
  output[1] = x1;
  output[2] = x2;
  output[3] = x3;
}

force_inline  inline static void Hacl_Symmetric_Salsa20_xor_(uint8_t *c, const uint8_t *m, const v32x4* b)
{
  STORE32x4(c, XOR32x4(LOAD32x4(m),b[0]));
  STORE32x4(c+16, XOR32x4(LOAD32x4(m+16),b[1]));
  STORE32x4(c+32, XOR32x4(LOAD32x4(m+32),b[2]));
  STORE32x4(c+48, XOR32x4(LOAD32x4(m+48),b[3]));
}

 inline static void Hacl_Symmetric_Salsa20_salsa20_xor(uint8_t *c, const uint8_t *m, const v32x4 *v)
{
  __attribute__ ((aligned (16))) v32x4 block[4];
  Hacl_Symmetric_Salsa20_salsa20(block, v);
  Hacl_Symmetric_Salsa20_xor_(c, m, block);
}

inline static uint64_t Hacl_Symmetric_Salsa20_incr_counter(v32x4 *v, uint64_t ctr)
{
  uint64_t ctr1 = ctr + (uint64_t )1;
  uint64_t sctr1 = ctr1;
  uint32_t c8 = (uint32_t )ctr1;
  uint32_t c9 = (uint32_t )(ctr1 >> (uint32_t )32);

  v[1] = (v32x4) {v[1][0],c9,v[1][2],v[1][3]};
  v[2] = (v32x4) {c8,v[2][1],v[2][2],v[2][3]};
  return ctr1;
}

inline static uint64_t
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_loop(
  uint8_t *c,
  const uint8_t *m,
  v32x4 *v,
  uint64_t ctr,
  uint64_t mlen
)
{
  if (mlen < (uint64_t )64)
    return mlen;
  else
  {
    Hacl_Symmetric_Salsa20_salsa20_xor(c, m, v);
    uint64_t ctr1 = Hacl_Symmetric_Salsa20_incr_counter(v,ctr);
    uint64_t mlen0 = mlen - (uint64_t )64;
    uint8_t *c_ = c + (uint32_t )64;
    const uint8_t *m_ = m + (uint32_t )64;
    return Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_loop(c_, m_, v, ctr1, mlen0);
  }
}

inline static void
Hacl_Symmetric_Salsa20_xor_bytes(uint8_t *x, const uint8_t *y, const uint8_t *b, uint32_t i, uint32_t len)
{
  uint32_t curr = i;
  uint32_t r = len - curr;
  if (r == (uint32_t )0)
    return;
  else 
  {
    x[curr] = y[curr] ^ b[curr];
    Hacl_Symmetric_Salsa20_xor_bytes(x, y, b, i + (uint32_t )1, len);
    return;
  }
}

inline static void
Hacl_Symmetric_Salsa20_salsa20_xor_partial(uint8_t *c, const uint8_t *m, const v32x4 *v, uint32_t len)
{
  __attribute__ ((aligned (16))) v32x4 o[4];
  __attribute__ ((aligned (16))) uint8_t block[16] = { 0 };

  Hacl_Symmetric_Salsa20_salsa20(o, v);
  Hacl_Symmetric_Salsa20_salsa20_finish(block, o);
  Hacl_Symmetric_Salsa20_xor_bytes(c, m, block, (uint32_t )0, len);
}

inline static void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_(
  uint8_t *c,
  const uint8_t *m,
  uint64_t mlen,
  const uint8_t *n,
  uint64_t ic,
  const uint8_t *k
)
{
  __attribute__ ((aligned (16))) v32x4 v[4];
  Hacl_Symmetric_Salsa20_salsa20_init(v, k, n, ic);
  uint64_t
  uu____4317 = Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_loop(c, m, v, ic, mlen);
  uint32_t mlen_ = (uint32_t )(mlen & (uint64_t )63);
  uint32_t off = (uint32_t )mlen - mlen_;
  if (mlen_ >= (uint32_t )0)
    Hacl_Symmetric_Salsa20_salsa20_xor_partial(c + off, m + off, v, mlen_);
}

inline static void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic(
  uint8_t *c,
  const uint8_t *m,
  uint64_t mlen,
  const uint8_t *n,
  uint64_t ic,
  const uint8_t *k
)
{
  if (mlen == (uint64_t )0)
    return;
  else
  {
    Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_(c, m, mlen, n, ic, k);
    return;
  }
}

inline static void Hacl_Symmetric_Salsa20_salsa20_store(uint8_t *c, v32x4 *v)
{
  __attribute__ ((aligned (16))) v32x4 o[4];
  Hacl_Symmetric_Salsa20_salsa20(o, v);
  STORE32x4(c,o[0]);
  STORE32x4(c+16,o[1]);
  STORE32x4(c+32,o[2]);
  STORE32x4(c+48,o[3]);
}

inline static uint64_t
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_loop(
  uint8_t *c,
  uint64_t clen,
  v32x4* v,
  uint64_t ctr
)
{
  if (clen < (uint64_t )64)
    return clen;
  else
  {
    Hacl_Symmetric_Salsa20_salsa20_store(c, v);
    uint64_t ctr1 = Hacl_Symmetric_Salsa20_incr_counter(v, ctr);
    uint64_t clen0 = clen - (uint64_t )64;
    uint8_t *c0 = c + (uint32_t )64;
    return Hacl_Symmetric_Salsa20_crypto_stream_salsa20_loop(c0, clen0, v, ctr1);
  }
}

inline static void
Hacl_Symmetric_Salsa20_store_bytes(uint8_t *x, uint8_t *b, uint32_t i, uint32_t len)
{
  uint32_t curr = i;
  uint32_t r = len - curr;
  if (r == (uint32_t )0)
    return;
  else
  {
    x[curr] = b[curr];
    Hacl_Symmetric_Salsa20_store_bytes(x, b, i + (uint32_t )1, len);
    return;
  }
}

inline static void
Hacl_Symmetric_Salsa20_salsa20_store_partial(uint8_t *c, v32x4 *v, uint32_t len)
{
  __attribute__ ((aligned (16))) v32x4 o[4];
  __attribute__ ((aligned (16))) uint8_t block[16] = { 0 };
  Hacl_Symmetric_Salsa20_salsa20(o, v);
  Hacl_Symmetric_Salsa20_salsa20_finish(block, o);
  Hacl_Symmetric_Salsa20_store_bytes(c, block, (uint32_t )0, len);
}

inline static void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20(uint8_t *c, uint64_t clen, uint8_t *n, uint8_t *k)
{
  if (clen == (uint64_t )0)
  {
    
  }
  else
  {
    uint32_t clen_ = (uint32_t )(clen & (uint64_t )63);
    uint32_t off = (uint32_t )clen - clen_;
    __attribute__ ((aligned (16))) v32x4 v[4];
    Hacl_Symmetric_Salsa20_salsa20_init(v, k, n, (uint64_t )0);
    uint64_t
    uu____5052 = Hacl_Symmetric_Salsa20_crypto_stream_salsa20_loop(c, clen, v, (uint64_t )0);
    if (clen_ >= (uint32_t )0)
      Hacl_Symmetric_Salsa20_salsa20_store_partial(c + off, v, clen_);
  }
}

void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic(c, m, mlen, n, (uint64_t )0, k);
  return;
}

void
Salsa20_crypto_stream_salsa20_xor_ic(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint64_t ic,
  uint8_t *k
)
{
  Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic(c, m, mlen, n, ic, k);
  return;
}

void Salsa20_crypto_stream_salsa20(uint8_t *c, uint64_t clen, uint8_t *n, uint8_t *k)
{
  Hacl_Symmetric_Salsa20_crypto_stream_salsa20(c, clen, n, k);
  return;
}

void
Salsa20_crypto_stream_salsa20_xor(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor(c, m, mlen, n, k);
  return;
}

