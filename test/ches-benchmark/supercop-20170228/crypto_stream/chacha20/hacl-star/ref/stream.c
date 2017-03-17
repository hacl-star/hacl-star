#include "kremlib.h"
#include "loops.h"
#include "crypto_stream.h"

inline static void
Hacl_Impl_Chacha20_uint32s_from_le_bytes(uint32_t *output, const uint8_t *input, uint32_t len)
{
  memcpy((uint8_t*)output,input,4*len);
}

inline static void
Hacl_Impl_Chacha20_uint32s_to_le_bytes(uint8_t *output, const uint32_t *input, uint32_t len)
{
  memcpy(output,(uint8_t*)input,4*len);
}

inline static void Hacl_Impl_Chacha20_constant_setup_(uint32_t *st)
{
  st[0] = (uint32_t )0x61707865;
  st[1] = (uint32_t )0x3320646e;
  st[2] = (uint32_t )0x79622d32;
  st[3] = (uint32_t )0x6b206574;
}

inline static void Hacl_Impl_Chacha20_constant_setup(uint32_t *st)
{
  Hacl_Impl_Chacha20_constant_setup_(st);
  return;
}

inline static void Hacl_Impl_Chacha20_keysetup(uint32_t *st, const uint8_t *k)
{
  Hacl_Impl_Chacha20_uint32s_from_le_bytes(st, k, (uint32_t )8);
  return;
}

inline static void Hacl_Impl_Chacha20_ivsetup(uint32_t *st, const uint8_t *iv)
{
  Hacl_Impl_Chacha20_uint32s_from_le_bytes(st, iv, (uint32_t )2);
  return;
}

inline static void Hacl_Impl_Chacha20_ctrsetup(uint32_t *st, uint32_t ctr)
{
  st[0] = ctr;
  st[1] = ctr;
}

inline static void Hacl_Impl_Chacha20_setup(uint32_t *st, const uint8_t *k, const uint8_t *n, uint32_t c)
{
  uint32_t *stcst = st;
  uint32_t *stk = st + (uint32_t )4;
  uint32_t *stc = st + (uint32_t )12;
  uint32_t *stn = st + (uint32_t )14;
  Hacl_Impl_Chacha20_constant_setup(stcst);
  Hacl_Impl_Chacha20_keysetup(stk, k);
  Hacl_Impl_Chacha20_ctrsetup(stc, c);
  Hacl_Impl_Chacha20_ivsetup(stn, n);
  return;
}

inline static void
Hacl_Impl_Chacha20_line(uint32_t *st, uint32_t a, uint32_t b, uint32_t d, uint32_t s)
{
  uint32_t sa0 = st[a];
  uint32_t sb = st[b];
  st[a] = sa0 + sb;
  uint32_t sd = st[d];
  uint32_t sa = st[a];
  uint32_t xx = sd ^ sa;
  st[d] = (xx << s) | (xx >> ((uint32_t)32 - s));
}

/*
inline static void
Hacl_Impl_Chacha20_quarter_round(uint32_t *st, uint32_t a, uint32_t b, uint32_t c, uint32_t d)
{
  Hacl_Impl_Chacha20_line(st, a, b, d, (uint32_t )16);
  Hacl_Impl_Chacha20_line(st, c, d, b, (uint32_t )12);
  Hacl_Impl_Chacha20_line(st, a, b, d, (uint32_t )8);
  Hacl_Impl_Chacha20_line(st, c, d, b, (uint32_t )7);
  return;
}
*/
inline static void
Hacl_Impl_Chacha20_quarter_round(
  uint32_t *ctx,
  uint32_t a,
  uint32_t b,
  uint32_t c,
  uint32_t d
)
{
  uint32_t xa0 = ctx[a];
  uint32_t xb0 = ctx[b];
  uint32_t xc0 = ctx[c];
  uint32_t xd0 = ctx[d];
  uint32_t xa1 = xa0 + xb0;
  uint32_t xd1 = xd0 ^ xa1;
  uint32_t xd2 = xd1 << (uint32_t )16 | xd1 >> (uint32_t )16;
  uint32_t xc1 = xc0 + xd2;
  uint32_t xb1 = xb0 ^ xc1;
  uint32_t xb2 = xb1 << (uint32_t )12 | xb1 >> (uint32_t )20;
  uint32_t xa = xa1 + xb2;
  uint32_t xd = xd2 ^ xa;
  uint32_t xd3 = xd << (uint32_t )8 | xd >> (uint32_t )24;
  uint32_t xc = xc1 + xd3;
  uint32_t xb = xb2 ^ xc;
  uint32_t xb3 = xb << (uint32_t )7 | xb >> (uint32_t )25;
  ctx[a] = xa;
  ctx[b] = xb3;
  ctx[c] = xc;
  ctx[d] = xd3;
}


inline static void Hacl_Impl_Chacha20_column_round(uint32_t *st)
{
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )0, (uint32_t )4, (uint32_t )8, (uint32_t )12);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )1, (uint32_t )5, (uint32_t )9, (uint32_t )13);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )2, (uint32_t )6, (uint32_t )10, (uint32_t )14);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )3, (uint32_t )7, (uint32_t )11, (uint32_t )15);
  return;
}

inline static void Hacl_Impl_Chacha20_diagonal_round(uint32_t *st)
{
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )0, (uint32_t )5, (uint32_t )10, (uint32_t )15);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )1, (uint32_t )6, (uint32_t )11, (uint32_t )12);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )2, (uint32_t )7, (uint32_t )8, (uint32_t )13);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )3, (uint32_t )4, (uint32_t )9, (uint32_t )14);
  return;
}

inline static void Hacl_Impl_Chacha20_double_round(uint32_t *st)
{
  Hacl_Impl_Chacha20_column_round(st);
  Hacl_Impl_Chacha20_diagonal_round(st);
  return;
}

inline static void Hacl_Impl_Chacha20_rounds(uint32_t *st)
{
  Hacl_Impl_Chacha20_double_round(st);
  Hacl_Impl_Chacha20_double_round(st);
  Hacl_Impl_Chacha20_double_round(st);
  Hacl_Impl_Chacha20_double_round(st);
  Hacl_Impl_Chacha20_double_round(st);
  Hacl_Impl_Chacha20_double_round(st);
  Hacl_Impl_Chacha20_double_round(st);
  Hacl_Impl_Chacha20_double_round(st);
  Hacl_Impl_Chacha20_double_round(st);
  Hacl_Impl_Chacha20_double_round(st);
  return;
}

inline static void Hacl_Impl_Chacha20_sum_states(uint32_t *st, const uint32_t *st_)
{
  sum_states(st, st_);
  return;
}

inline static void Hacl_Impl_Chacha20_copy_state(uint32_t *st, const uint32_t *st_)
{
  memcpy(st, st_, (uint32_t )16 * sizeof st_[0]);
}

inline static void
Hacl_Impl_Chacha20_chacha20_core(void *log, uint32_t *nst, uint32_t *st, uint32_t ctr)
{
  st[12] = ctr;
  Hacl_Impl_Chacha20_copy_state(nst, st);
  Hacl_Impl_Chacha20_rounds(nst);
  Hacl_Impl_Chacha20_sum_states(nst, st);
  return;
}

inline static void
Hacl_Impl_Chacha20_chacha20_xor_block(void *log, uint8_t *out, uint32_t *st, const uint8_t* in, uint32_t ctr)
{
  uint32_t st_[16] = { 0 };
  Hacl_Impl_Chacha20_chacha20_core(log, st_,st, ctr);
  for (int i = 0; i < 16; i++) {
    store32_le(out+(4*i), st_[i] ^ load32_le(in+(4*i)));
  }
  return;
}


static void
Hacl_Impl_Chacha20_update_last(
  uint8_t *output,
  const uint8_t *plain,
  uint32_t len,
  void *log,
  uint32_t *st,
  uint32_t ctr
)
{
  uint8_t block[64] = { 0 };
  uint32_t st_[16] = { 0 };
  Hacl_Impl_Chacha20_chacha20_core(log, st_,st, ctr);
  Hacl_Impl_Chacha20_uint32s_to_le_bytes(block, st_, (uint32_t )16);
  xor_bytes(output, plain, block, len);
}



inline static void Hacl_Impl_Chacha20_init(uint32_t *st, const uint8_t *k, const uint8_t *n)
{
  Hacl_Impl_Chacha20_setup(st, k, n, (uint32_t )0);
  return;
}


inline static void
Hacl_Impl_Chacha20_update(
  uint8_t *output,
  const uint8_t *plain,
  void *log,
  uint32_t *st,
  uint32_t ctr
)
{
  Hacl_Impl_Chacha20_chacha20_xor_block((void *)(uint8_t )0, output, st, plain, ctr);
}

inline static void
Hacl_Impl_Chacha20_chacha20_counter_mode_(
  uint8_t *output,
  const uint8_t *plain,
  uint32_t len,
  void *log,
  uint32_t *st,
  uint32_t ctr
)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    void
    *uu____3030 =
      (Hacl_Impl_Chacha20_update_last(output, plain, len, (void *)(uint8_t )0, st, ctr) , (void *)0);
    return;
  }
}

inline static void
Hacl_Impl_Chacha20_chacha20_counter_mode(
  uint8_t *output,
  const uint8_t *plain,
  uint32_t len,
  void *log,
  uint32_t *st,
  uint32_t ctr
)
{
  if (len <= (uint32_t )64)
  {
    Hacl_Impl_Chacha20_chacha20_counter_mode_(output, plain, len, (void *)(uint8_t )0, st, ctr);
    return;
  }
  else
  {
    const uint8_t *b = plain;
    const uint8_t *b_ = plain + (uint32_t )64;
    uint8_t *o = output;
    uint8_t *o_ = output + (uint32_t )64;
    void *log_ = (Hacl_Impl_Chacha20_update(o, b, (void *)(uint8_t )0, st, ctr) , (void *)0);
    Hacl_Impl_Chacha20_chacha20_counter_mode(o_,
      b_,
      len - (uint32_t )64,
      (void *)(uint8_t )0,
      st,
      ctr + (uint32_t )1);
    return;
  }
}

inline static void
Hacl_Impl_Chacha20_chacha20(
  uint8_t *output,
  const uint8_t *plain,
  uint32_t len,
  const uint8_t *k,
  const uint8_t *n,
  uint32_t ctr
)
{
  uint32_t buf[16] = { 0 };
  uint32_t
  *st =
    /* start inlining Hacl.Impl.Chacha20.alloc */ buf /* end inlining Hacl.Impl.Chacha20.alloc */;
  void *l = (Hacl_Impl_Chacha20_init(st, k, n) , (void *)0);
  Hacl_Impl_Chacha20_chacha20_counter_mode(output, plain, len, (void *)(uint8_t )0, st, ctr);
}

static void Chacha_double_round(uint32_t *st)
{
  Hacl_Impl_Chacha20_double_round(st);
  return;
}

void
Chacha_chacha20(
  uint8_t *output,
  const uint8_t *plain,
  uint32_t len,
  const uint8_t *k,
  const uint8_t *n,
  uint32_t ctr
)
{
  Hacl_Impl_Chacha20_chacha20(output, plain, len, k, n, ctr);
  return;
}

int crypto_stream_xor(
        unsigned char *out,
        const unsigned char *in,
        unsigned long long inlen,
        const unsigned char *n,
        const unsigned char *k
		      ){

  Hacl_Impl_Chacha20_chacha20(out, in, inlen, k, n, 0);
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
