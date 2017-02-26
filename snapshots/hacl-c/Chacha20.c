#include "Chacha20.h"

static void
Hacl_Impl_Chacha20_uint32s_from_le_bytes(uint32_t *output, uint8_t *input, uint32_t len)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    uint8_t *x0 = input;
    uint32_t
    _0_41 =
      /* start inlining Hacl.Endianness.hload32_le */
        /* start inlining Hacl.Endianness.load32_le */
          load32_le(x0)
        /* end inlining Hacl.Endianness.load32_le */
      /* end inlining Hacl.Endianness.hload32_le */;
    output[0] = _0_41;
    uint32_t *output_ = output + (uint32_t )1;
    uint8_t *input_ = input + (uint32_t )4;
    Hacl_Impl_Chacha20_uint32s_from_le_bytes(output_, input_, len - (uint32_t )1);
    return;
  }
}

static void
Hacl_Impl_Chacha20_uint32s_to_le_bytes(uint8_t *output, uint32_t *input, uint32_t len)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    uint32_t hd = input[0];
    uint8_t *x0 = output;
    /* start inlining Hacl.Endianness.hstore32_le */
    /* start inlining Hacl.Endianness.store32_le */
    store32_le(x0, hd);
    /* end inlining Hacl.Endianness.store32_le */
    /* end inlining Hacl.Endianness.hstore32_le */
    uint8_t *output_ = output + (uint32_t )4;
    uint32_t *input_ = input + (uint32_t )1;
    Hacl_Impl_Chacha20_uint32s_to_le_bytes(output_, input_, len - (uint32_t )1);
    return;
  }
}

inline static void Hacl_Impl_Chacha20_setup(uint32_t *st, uint8_t *k, uint8_t *n, uint32_t c)
{
  uint32_t *stcst = st;
  uint32_t *stk = st + (uint32_t )4;
  uint32_t *stc = st + (uint32_t )12;
  uint32_t *stn = st + (uint32_t )13;
  stcst[0] = (uint32_t )0x61707865;
  stcst[1] = (uint32_t )0x3320646e;
  stcst[2] = (uint32_t )0x79622d32;
  stcst[3] = (uint32_t )0x6b206574;
  /* start inlining Hacl.Impl.Chacha20.constant_setup */
  /* start inlining Hacl.Impl.Chacha20.constant_setup_ */
  /* end inlining Hacl.Impl.Chacha20.constant_setup_ */
  /* end inlining Hacl.Impl.Chacha20.constant_setup */
  /* start inlining Hacl.Impl.Chacha20.keysetup */
  Hacl_Impl_Chacha20_uint32s_from_le_bytes(stk, k, (uint32_t )8);
  /* end inlining Hacl.Impl.Chacha20.keysetup */
  stc[0] = c;
  /* start inlining Hacl.Impl.Chacha20.ctrsetup */
  /* end inlining Hacl.Impl.Chacha20.ctrsetup */
  /* start inlining Hacl.Impl.Chacha20.ivsetup */
  Hacl_Impl_Chacha20_uint32s_from_le_bytes(stn, n, (uint32_t )3);
  return;
  /* end inlining Hacl.Impl.Chacha20.ivsetup */
}

inline static void
Hacl_Impl_Chacha20_quarter_round(uint32_t *st, uint32_t a, uint32_t b, uint32_t c, uint32_t d)
{
  uint32_t sa0 = st[a];
  uint32_t sb0 = st[b];
  st[a] = sa0 + sb0;
  uint32_t sd = st[d];
  uint32_t sa1 = st[a];
  st[d] = (sd ^ sa1) << (uint32_t )16 | (sd ^ sa1) >> (uint32_t )32 - (uint32_t )16;
  /* start inlining Hacl.Impl.Chacha20.line */
  /* end inlining Hacl.Impl.Chacha20.line */
  uint32_t sa2 = st[c];
  uint32_t sb1 = st[d];
  st[c] = sa2 + sb1;
  uint32_t sd0 = st[b];
  uint32_t sa3 = st[c];
  st[b] = (sd0 ^ sa3) << (uint32_t )12 | (sd0 ^ sa3) >> (uint32_t )32 - (uint32_t )12;
  /* start inlining Hacl.Impl.Chacha20.line */
  /* end inlining Hacl.Impl.Chacha20.line */
  uint32_t sa4 = st[a];
  uint32_t sb2 = st[b];
  st[a] = sa4 + sb2;
  uint32_t sd1 = st[d];
  uint32_t sa5 = st[a];
  st[d] = (sd1 ^ sa5) << (uint32_t )8 | (sd1 ^ sa5) >> (uint32_t )32 - (uint32_t )8;
  /* start inlining Hacl.Impl.Chacha20.line */
  /* end inlining Hacl.Impl.Chacha20.line */
  /* start inlining Hacl.Impl.Chacha20.line */
  uint32_t sa6 = st[c];
  uint32_t sb = st[d];
  st[c] = sa6 + sb;
  uint32_t sd2 = st[b];
  uint32_t sa = st[c];
  st[b] = (sd2 ^ sa) << (uint32_t )7 | (sd2 ^ sa) >> (uint32_t )32 - (uint32_t )7;
  /* end inlining Hacl.Impl.Chacha20.line */
}

inline static void Hacl_Impl_Chacha20_double_round(uint32_t *st)
{
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )0, (uint32_t )4, (uint32_t )8, (uint32_t )12);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )1, (uint32_t )5, (uint32_t )9, (uint32_t )13);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )2, (uint32_t )6, (uint32_t )10, (uint32_t )14);
  /* start inlining Hacl.Impl.Chacha20.column_round */
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )3, (uint32_t )7, (uint32_t )11, (uint32_t )15);
  /* end inlining Hacl.Impl.Chacha20.column_round */
  /* start inlining Hacl.Impl.Chacha20.diagonal_round */
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )0, (uint32_t )5, (uint32_t )10, (uint32_t )15);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )1, (uint32_t )6, (uint32_t )11, (uint32_t )12);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )2, (uint32_t )7, (uint32_t )8, (uint32_t )13);
  Hacl_Impl_Chacha20_quarter_round(st, (uint32_t )3, (uint32_t )4, (uint32_t )9, (uint32_t )14);
  return;
  /* end inlining Hacl.Impl.Chacha20.diagonal_round */
}

inline static void Hacl_Impl_Chacha20_rounds(uint32_t *st)
{
  rounds(st);
  return;
}

inline static void Hacl_Impl_Chacha20_sum_states(uint32_t *st, uint32_t *st_)
{
  sum_states(st, st_);
  return;
}

inline static void Hacl_Impl_Chacha20_copy_state(uint32_t *st, uint32_t *st_)
{
  memcpy(st, st_, (uint32_t )16 * sizeof st_[0]);
}

inline static void
Hacl_Impl_Chacha20_chacha20_block(void *log, uint8_t *stream_block, uint32_t *st, uint32_t ctr)
{
  uint32_t st_[16] = { 0 };
  st[12] = ctr;
  Hacl_Impl_Chacha20_copy_state(st_, st);
  Hacl_Impl_Chacha20_rounds(st_);
  Hacl_Impl_Chacha20_sum_states(st_, st);
  Hacl_Impl_Chacha20_uint32s_to_le_bytes(stream_block, st_, (uint32_t )16);
  return;
}

inline static void Hacl_Impl_Chacha20_init(uint32_t *st, uint8_t *k, uint8_t *n)
{
  Hacl_Impl_Chacha20_setup(st, k, n, (uint32_t )0);
  return;
}

static void
Hacl_Impl_Chacha20_update_last(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  void *log,
  uint32_t *st,
  uint32_t ctr
)
{
  uint8_t block[64] = { 0 };
  void *l = (Hacl_Impl_Chacha20_chacha20_block((void *)(uint8_t )0, block, st, ctr) , (void *)0);
  uint8_t *mask = block;
  xor_bytes(output, plain, mask, len);
}

static void
Hacl_Impl_Chacha20_update(
  uint8_t *output,
  uint8_t *plain,
  void *log,
  uint32_t *st,
  uint32_t ctr
)
{
  uint8_t block[64] = { 0 };
  void *l = (Hacl_Impl_Chacha20_chacha20_block((void *)(uint8_t )0, block, st, ctr) , (void *)0);
  xor_bytes(output, plain, block, (uint32_t )64);
}

static void
Hacl_Impl_Chacha20_chacha20_counter_mode_(
  uint8_t *output,
  uint8_t *plain,
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
    *uu____3016 =
      (Hacl_Impl_Chacha20_update_last(output, plain, len, (void *)(uint8_t )0, st, ctr) , (void *)0);
    return;
  }
}

static void
Hacl_Impl_Chacha20_chacha20_counter_mode(
  uint8_t *output,
  uint8_t *plain,
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
    uint8_t *b = plain;
    uint8_t *b_ = plain + (uint32_t )64;
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

static void
Hacl_Impl_Chacha20_chacha20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n,
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

void Chacha20_double_round(uint32_t *st)
{
  Hacl_Impl_Chacha20_double_round(st);
  return;
}

void
Chacha20_chacha20_key_block(
  uint8_t *block,
  uint8_t *k,
  uint8_t *n,
  uint32_t ctr
)
{
  uint32_t st[16] = { 0 };
  void *l = (Hacl_Impl_Chacha20_init(st, k, n) , (void *)0);
  l = (Hacl_Impl_Chacha20_chacha20_block((void *)(uint8_t )0, block, st, ctr) , (void *)0);
  return;
}


void
Chacha20_chacha20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n,
  uint32_t ctr
)
{
  Hacl_Impl_Chacha20_chacha20(output, plain, len, k, n, ctr);
  return;
}

