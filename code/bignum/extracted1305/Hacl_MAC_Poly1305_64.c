#include "Hacl_MAC_Poly1305_64.h"

uint64_t
*Hacl_MAC_Poly1305_64___proj__MkState__item__r(Hacl_MAC_Poly1305_64_poly1305_state projectee)
{
  Hacl_MAC_Poly1305_64_poly1305_state scrut = projectee;
  uint64_t *r = scrut.x00;
  uint64_t *h = scrut.x01;
  return r;
}

uint64_t
*Hacl_MAC_Poly1305_64___proj__MkState__item__h(Hacl_MAC_Poly1305_64_poly1305_state projectee)
{
  Hacl_MAC_Poly1305_64_poly1305_state scrut = projectee;
  uint64_t *r = scrut.x00;
  uint64_t *h = scrut.x01;
  return h;
}

uint64_t Hacl_MAC_Poly1305_64_load64_le(uint8_t *b)
{
  uint8_t b0 = b[(uint32_t )0];
  uint8_t b1 = b[(uint32_t )1];
  uint8_t b2 = b[(uint32_t )2];
  uint8_t b3 = b[(uint32_t )3];
  uint8_t b4 = b[(uint32_t )4];
  uint8_t b5 = b[(uint32_t )5];
  uint8_t b6 = b[(uint32_t )6];
  uint8_t b7 = b[(uint32_t )7];
  return
    (uint64_t )b0
    | (uint64_t )b1 << (uint32_t )8
    | (uint64_t )b2 << (uint32_t )16
    | (uint64_t )b3 << (uint32_t )24
    | (uint64_t )b4 << (uint32_t )32
    | (uint64_t )b5 << (uint32_t )40
    | (uint64_t )b6 << (uint32_t )48
    | (uint64_t )b7 << (uint32_t )56;
}

void Hacl_MAC_Poly1305_64_store64_le(uint8_t *b, uint64_t z)
{
  uint8_t b0 = (uint8_t )z;
  uint8_t b1 = (uint8_t )(z >> (uint32_t )8);
  uint8_t b2 = (uint8_t )(z >> (uint32_t )16);
  uint8_t b3 = (uint8_t )(z >> (uint32_t )24);
  uint8_t b4 = (uint8_t )(z >> (uint32_t )32);
  uint8_t b5 = (uint8_t )(z >> (uint32_t )40);
  uint8_t b6 = (uint8_t )(z >> (uint32_t )48);
  uint8_t b7 = (uint8_t )(z >> (uint32_t )56);
  b[(uint32_t )0] = b0;
  b[(uint32_t )1] = b1;
  b[(uint32_t )2] = b2;
  b[(uint32_t )3] = b3;
  b[(uint32_t )4] = b4;
  b[(uint32_t )5] = b5;
  b[(uint32_t )6] = b6;
  b[(uint32_t )7] = b7;
}

void *Hacl_MAC_Poly1305_64_sel_word(FStar_HyperStack_mem h, uint8_t *b)
{
  return (void *)(uint8_t )0;
}

Prims_nat Hacl_MAC_Poly1305_64_sel_int(FStar_HyperStack_mem h, uint64_t *b)
{
  return (Prims_nat )(uint8_t )0;
}

uint64_t Hacl_MAC_Poly1305_64_mk_mask(uint32_t nbits)
{
  return ((uint64_t )1 << nbits) - (uint64_t )1;
}

void Hacl_MAC_Poly1305_64_poly1305_encode_r(uint64_t *r, uint8_t *key)
{
  uint64_t t0 = Hacl_MAC_Poly1305_64_load64_le(key + (uint32_t )0);
  uint64_t t1 = Hacl_MAC_Poly1305_64_load64_le(key + (uint32_t )8);
  uint64_t r0 = t0 & (uint64_t )0xffc0fffffff;
  uint64_t r1 = (t0 >> (uint32_t )44 | t1 << (uint32_t )20) & (uint64_t )0xfffffc0ffff;
  uint64_t r2 = t1 >> (uint32_t )24 & (uint64_t )0x00ffffffc0f;
  r[(uint32_t )0] = r0;
  r[(uint32_t )1] = r1;
  r[(uint32_t )2] = r2;
}

void Hacl_MAC_Poly1305_64_toField(uint64_t *b, uint8_t *m)
{
  uint64_t t0 = Hacl_MAC_Poly1305_64_load64_le(m);
  uint64_t t1 = Hacl_MAC_Poly1305_64_load64_le(m + (uint32_t )8);
  uint64_t mask_2_44 = Hacl_MAC_Poly1305_64_mk_mask((uint32_t )44);
  uint64_t mask_2_42 = Hacl_MAC_Poly1305_64_mk_mask((uint32_t )42);
  uint64_t t_0 = t0 & mask_2_44;
  uint64_t t_1 = (t0 >> (uint32_t )44 | t1 << (uint32_t )20) & mask_2_44;
  uint64_t t_2 = t1 >> (uint32_t )24 & mask_2_42;
  b[(uint32_t )0] = t_0;
  b[(uint32_t )1] = t_1;
  b[(uint32_t )2] = t_2;
}

void Hacl_MAC_Poly1305_64_toField_plus_2_128(uint64_t *b, uint8_t *m)
{
  Hacl_MAC_Poly1305_64_toField(b, m);
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b20 = b2 | (uint64_t )1 << (uint32_t )40;
  b[(uint32_t )2] = b20;
}

void Hacl_MAC_Poly1305_64_toField_plus(uint32_t len, uint64_t *b, uint8_t *m_)
{
  uint8_t m[16] = { 0 };
  memcpy(m, m_, len * sizeof m_[0]);
  Hacl_MAC_Poly1305_64_toField(b, m);
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b20 = b2 | (uint64_t )1 << (uint32_t )24 + len;
  b[(uint32_t )2] = b20;
}

void Hacl_MAC_Poly1305_64_add_and_multiply(uint64_t *acc, uint64_t *block, uint64_t *r)
{
  Hacl_Bignum_Fsum_fsum_(acc, block, (uint32_t )3);
  Hacl_Bignum_Fmul_fmul(acc, acc, r);
  return;
}

void Hacl_MAC_Poly1305_64_poly1305_finish(uint8_t *mac, uint64_t *acc, uint8_t *key_s)
{
  uint64_t tmp[3] = { 0 };
  uint64_t mask_2_42 = (uint64_t )0x3ffffffffff;
  Hacl_Bignum_Fproduct_carry_limb_(acc, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top(acc);
  Hacl_Bignum_Fproduct_carry_0_to_1(acc);
  Hacl_MAC_Poly1305_64_toField(tmp, key_s);
  Hacl_Bignum_Fsum_fsum_(acc, tmp, (uint32_t )3);
  Hacl_Bignum_Fproduct_carry_limb_(acc, (uint32_t )0);
  uint64_t h00 = acc[(uint32_t )0];
  uint64_t h10 = acc[(uint32_t )1];
  uint64_t h2 = acc[(uint32_t )2];
  uint64_t h0 = h00 | h10 << (uint32_t )44;
  uint64_t h1 = h10 >> (uint32_t )20 | (h2 & mask_2_42) << (uint32_t )24;
  Hacl_MAC_Poly1305_64_store64_le(mac, h0);
  Hacl_MAC_Poly1305_64_store64_le(mac + (uint32_t )8, h1);
}

void Hacl_MAC_Poly1305_64_poly1305_start(uint64_t *a)
{
  a[(uint32_t )0] = (uint64_t )0;
  a[(uint32_t )1] = (uint64_t )0;
  a[(uint32_t )2] = (uint64_t )0;
}

void Hacl_MAC_Poly1305_64_poly1305_init(uint64_t *r, uint8_t *s, uint8_t *key)
{
  uint64_t t0 = Hacl_MAC_Poly1305_64_load64_le(key);
  uint64_t t1 = Hacl_MAC_Poly1305_64_load64_le(key + (uint32_t )8);
  r[(uint32_t )0] = t0 & (uint64_t )0xffc0fffffff;
  r[(uint32_t )1] = (t0 >> (uint32_t )44 | t1 << (uint32_t )20) & (uint64_t )0xfffffc0ffff;
  r[(uint32_t )2] = t1 >> (uint32_t )24 & (uint64_t )0x00ffffffc0f;
  memcpy(s, key + (uint32_t )16, (uint32_t )16 * sizeof key[0]);
}

void Hacl_MAC_Poly1305_64_poly1305_init_(Hacl_MAC_Poly1305_64_poly1305_state st, uint8_t *key)
{
  uint64_t t0 = Hacl_MAC_Poly1305_64_load64_le(key);
  uint64_t t1 = Hacl_MAC_Poly1305_64_load64_le(key + (uint32_t )8);
  Hacl_MAC_Poly1305_64___proj__MkState__item__r(st)[(uint32_t )0] = t0 & (uint64_t )0xffc0fffffff;
  Hacl_MAC_Poly1305_64___proj__MkState__item__r(st)[(uint32_t )1] =
    (t0 >> (uint32_t )44 | t1 << (uint32_t )20)
    & (uint64_t )0xfffffc0ffff;
  Hacl_MAC_Poly1305_64___proj__MkState__item__r(st)[(uint32_t )2] =
    t1
    >> (uint32_t )24
    & (uint64_t )0x00ffffffc0f;
  Hacl_MAC_Poly1305_64___proj__MkState__item__h(st)[(uint32_t )0] = (uint64_t )0;
  Hacl_MAC_Poly1305_64___proj__MkState__item__h(st)[(uint32_t )1] = (uint64_t )0;
  Hacl_MAC_Poly1305_64___proj__MkState__item__h(st)[(uint32_t )2] = (uint64_t )0;
}

void
Hacl_MAC_Poly1305_64_poly1305_update(
  void *log,
  Hacl_MAC_Poly1305_64_poly1305_state st,
  uint8_t *m
)
{
  uint64_t tmp[3] = { 0 };
  uint64_t *acc = Hacl_MAC_Poly1305_64___proj__MkState__item__h(st);
  uint64_t *r = Hacl_MAC_Poly1305_64___proj__MkState__item__r(st);
  Hacl_MAC_Poly1305_64_toField_plus_2_128(tmp, m);
  Hacl_MAC_Poly1305_64_add_and_multiply(acc, tmp, r);
}

void
Hacl_MAC_Poly1305_64_poly1305_blocks(
  void *log,
  Hacl_MAC_Poly1305_64_poly1305_state st,
  uint8_t *m,
  uint64_t len
)
{
  if (len < (uint64_t )16)
    return;
  else
  {
    void *new_log = (Hacl_MAC_Poly1305_64_poly1305_update((uint8_t )0, st, m) , (void *)0);
    uint64_t len0 = len - (uint64_t )16;
    uint8_t *m0 = m + (uint32_t )16;
    Hacl_MAC_Poly1305_64_poly1305_blocks((uint8_t )0, st, m0, len0);
    return;
  }
}

void
Hacl_MAC_Poly1305_64_poly1305_finish_(
  void *log,
  Hacl_MAC_Poly1305_64_poly1305_state st,
  uint8_t *mac,
  uint8_t *m,
  uint64_t len,
  uint8_t *key_s
)
{
  uint64_t mask_2_42 = (uint64_t )0x3ffffffffff;
  uint64_t tmp[3] = { 0 };
  uint64_t rem_ = len & (uint64_t )0xf;
  if (rem_ == (uint64_t )0)
  {
    
  }
  else
  {
    uint8_t zero = (uint8_t )0;
    uint8_t block[16];
    for (uintmax_t i = 0; i < (uint32_t )16; ++i)
      block[i] = zero;
    uint32_t i = (uint32_t )rem_;
    memcpy(block, m + (uint32_t )(len - rem_), i * sizeof m[0]);
    block[i] = (uint8_t )1;
    Hacl_MAC_Poly1305_64_toField(tmp, block);
    Hacl_MAC_Poly1305_64_add_and_multiply(Hacl_MAC_Poly1305_64___proj__MkState__item__h(st),
      tmp,
      Hacl_MAC_Poly1305_64___proj__MkState__item__r(st));
  }
  Hacl_Bignum_Fproduct_carry_limb_(Hacl_MAC_Poly1305_64___proj__MkState__item__h(st),
    (uint32_t )0);
  Hacl_Bignum_Fproduct_carry_0_to_1(Hacl_MAC_Poly1305_64___proj__MkState__item__h(st));
  Hacl_MAC_Poly1305_64_toField(tmp, key_s);
  Hacl_Bignum_Fsum_fsum_(Hacl_MAC_Poly1305_64___proj__MkState__item__h(st), tmp, (uint32_t )3);
  Hacl_Bignum_Fproduct_carry_limb_(Hacl_MAC_Poly1305_64___proj__MkState__item__h(st),
    (uint32_t )0);
  uint64_t h00 = Hacl_MAC_Poly1305_64___proj__MkState__item__h(st)[(uint32_t )0];
  uint64_t h10 = Hacl_MAC_Poly1305_64___proj__MkState__item__h(st)[(uint32_t )1];
  uint64_t h2 = Hacl_MAC_Poly1305_64___proj__MkState__item__h(st)[(uint32_t )2];
  uint64_t h0 = h00 | h10 << (uint32_t )44;
  uint64_t h1 = h10 >> (uint32_t )20 | (h2 & mask_2_42) << (uint32_t )24;
  Hacl_MAC_Poly1305_64_store64_le(mac, h0);
  Hacl_MAC_Poly1305_64_store64_le(mac + (uint32_t )8, h1);
}

void
Hacl_MAC_Poly1305_64_crypto_onetimeauth(
  uint8_t *output,
  uint8_t *input,
  uint64_t len,
  uint8_t *k
)
{
  uint64_t zero = (uint64_t )0;
  uint64_t r[3];
  for (uintmax_t i = 0; i < (uint32_t )3; ++i)
    r[i] = zero;
  uint64_t h[3];
  for (uintmax_t i = 0; i < (uint32_t )3; ++i)
    h[i] = zero;
  Hacl_MAC_Poly1305_64_poly1305_state st = { .x00 = r, .x01 = h };
  uint8_t *key_r = k + (uint32_t )0;
  uint8_t *key_s = k + (uint32_t )16;
  void *init_log = (Hacl_MAC_Poly1305_64_poly1305_init_(st, key_r) , (void *)0);
  void
  *partial_log = (Hacl_MAC_Poly1305_64_poly1305_blocks((uint8_t )0, st, input, len) , (void *)0);
  void
  *final_log =
    (Hacl_MAC_Poly1305_64_poly1305_finish_((uint8_t )0, st, output, input, len, key_s) , (void *)0);
}

