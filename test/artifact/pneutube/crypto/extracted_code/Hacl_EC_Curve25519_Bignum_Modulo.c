#include "Hacl_EC_Curve25519_Bignum_Modulo.h"

FStar_UInt128_t Hacl_EC_Curve25519_Bignum_Modulo_times_wide_19(FStar_UInt128_t x)
{
  return
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(x, FStar_UInt128_shift_left(x, (uint32_t )4)),
      FStar_UInt128_shift_left(x, (uint32_t )1));
}

void Hacl_EC_Curve25519_Bignum_Modulo_freduce_degree_(FStar_UInt128_t *b)
{
  FStar_UInt128_t b0 = b[(uint32_t )0];
  FStar_UInt128_t b1 = b[(uint32_t )1];
  FStar_UInt128_t b2 = b[(uint32_t )2];
  FStar_UInt128_t b3 = b[(uint32_t )3];
  FStar_UInt128_t b5 = b[(uint32_t )5];
  FStar_UInt128_t b6 = b[(uint32_t )6];
  FStar_UInt128_t b7 = b[(uint32_t )7];
  FStar_UInt128_t b8 = b[(uint32_t )8];
  FStar_UInt128_t
  b0_ =
    FStar_UInt128_add_mod(b0,
      FStar_UInt128_add_mod(FStar_UInt128_add_mod(b5, FStar_UInt128_shift_left(b5, (uint32_t )4)),
        FStar_UInt128_shift_left(b5, (uint32_t )1)));
  FStar_UInt128_t
  b1_ =
    FStar_UInt128_add_mod(b1,
      FStar_UInt128_add_mod(FStar_UInt128_add_mod(b6, FStar_UInt128_shift_left(b6, (uint32_t )4)),
        FStar_UInt128_shift_left(b6, (uint32_t )1)));
  FStar_UInt128_t
  b2_ =
    FStar_UInt128_add_mod(b2,
      FStar_UInt128_add_mod(FStar_UInt128_add_mod(b7, FStar_UInt128_shift_left(b7, (uint32_t )4)),
        FStar_UInt128_shift_left(b7, (uint32_t )1)));
  FStar_UInt128_t
  b3_ =
    FStar_UInt128_add_mod(b3,
      FStar_UInt128_add_mod(FStar_UInt128_add_mod(b8, FStar_UInt128_shift_left(b8, (uint32_t )4)),
        FStar_UInt128_shift_left(b8, (uint32_t )1)));
  b[(uint32_t )0] = b0_;
  b[(uint32_t )1] = b1_;
  b[(uint32_t )2] = b2_;
  b[(uint32_t )3] = b3_;
}

void Hacl_EC_Curve25519_Bignum_Modulo_freduce_degree(FStar_UInt128_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_freduce_degree_(b);
  return;
}

FStar_UInt128_t Hacl_EC_Curve25519_Bignum_Modulo_mod_wide_2_51(FStar_UInt128_t a)
{
  return FStar_UInt128_logand(a, FStar_Int_Cast_uint64_to_uint128((uint64_t )0x7ffffffffffff));
}

void
Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_1_0(
  FStar_UInt128_t *b,
  FStar_UInt128_t b0,
  FStar_UInt128_t b1,
  FStar_UInt128_t b2,
  FStar_UInt128_t b3,
  FStar_UInt128_t b4
)
{
  FStar_UInt128_t
  b0_ = FStar_UInt128_logand(b0, FStar_Int_Cast_uint64_to_uint128((uint64_t )0x7ffffffffffff));
  FStar_UInt128_t r0 = FStar_UInt128_shift_right(b0, (uint32_t )51);
  FStar_UInt128_t
  b1_ =
    FStar_UInt128_logand(FStar_UInt128_add_mod(b1, r0),
      FStar_Int_Cast_uint64_to_uint128((uint64_t )0x7ffffffffffff));
  FStar_UInt128_t r1 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(b1, r0), (uint32_t )51);
  FStar_UInt128_t
  b2_ =
    FStar_UInt128_logand(FStar_UInt128_add_mod(b2, r1),
      FStar_Int_Cast_uint64_to_uint128((uint64_t )0x7ffffffffffff));
  FStar_UInt128_t r2 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(b2, r1), (uint32_t )51);
  FStar_UInt128_t
  b3_ =
    FStar_UInt128_logand(FStar_UInt128_add_mod(b3, r2),
      FStar_Int_Cast_uint64_to_uint128((uint64_t )0x7ffffffffffff));
  FStar_UInt128_t r3 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(b3, r2), (uint32_t )51);
  FStar_UInt128_t
  b4_ =
    FStar_UInt128_logand(FStar_UInt128_add_mod(b4, r3),
      FStar_Int_Cast_uint64_to_uint128((uint64_t )0x7ffffffffffff));
  FStar_UInt128_t b5_ = FStar_UInt128_shift_right(FStar_UInt128_add_mod(b4, r3), (uint32_t )51);
  Hacl_EC_Curve25519_Utils_update_wide_6(b, b0_, b1_, b2_, b3_, b4_, b5_);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_1_(FStar_UInt128_t *b)
{
  FStar_UInt128_t b0 = b[(uint32_t )0];
  FStar_UInt128_t b1 = b[(uint32_t )1];
  FStar_UInt128_t b2 = b[(uint32_t )2];
  FStar_UInt128_t b3 = b[(uint32_t )3];
  FStar_UInt128_t b4 = b[(uint32_t )4];
  Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_1_0(b, b0, b1, b2, b3, b4);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_1(FStar_UInt128_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_1_(b);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_2_(FStar_UInt128_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_1_(b);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_2(FStar_UInt128_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_2_(b);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_top_(FStar_UInt128_t *b)
{
  FStar_UInt128_t b0 = b[(uint32_t )0];
  FStar_UInt128_t b5 = b[(uint32_t )5];
  b[(uint32_t )0] =
    FStar_UInt128_add_mod(b0,
      FStar_UInt128_add_mod(FStar_UInt128_add_mod(b5, FStar_UInt128_shift_left(b5, (uint32_t )4)),
        FStar_UInt128_shift_left(b5, (uint32_t )1)));
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_top_1(FStar_UInt128_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_top_(b);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_top_2(FStar_UInt128_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_top_(b);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_0_to_1_(FStar_UInt128_t *b)
{
  FStar_UInt128_t b0 = b[(uint32_t )0];
  FStar_UInt128_t b1 = b[(uint32_t )1];
  FStar_UInt128_t
  b0_ = FStar_UInt128_logand(b0, FStar_Int_Cast_uint64_to_uint128((uint64_t )0x7ffffffffffff));
  FStar_UInt128_t r0 = FStar_UInt128_shift_right(b0, (uint32_t )51);
  b[(uint32_t )0] = b0_;
  b[(uint32_t )1] = FStar_UInt128_add_mod(b1, r0);
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_0_to_1(FStar_UInt128_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_0_to_1_(b);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_freduce_coefficients_wide(FStar_UInt128_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_1(b);
  Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_top_1(b);
  Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_2(b);
  Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_top_2(b);
  Hacl_EC_Curve25519_Bignum_Modulo_carry_wide_0_to_1(b);
  return;
}

uint64_t Hacl_EC_Curve25519_Bignum_Modulo_times_19(uint64_t x)
{
  return x + (x << (uint32_t )4) + (x << (uint32_t )1);
}

uint64_t Hacl_EC_Curve25519_Bignum_Modulo_mod_2_51(uint64_t a)
{
  return a & (uint64_t )0x7ffffffffffff;
}

void
Hacl_EC_Curve25519_Bignum_Modulo_carry_1_0_(
  uint64_t *b,
  uint64_t b0,
  uint64_t b1,
  uint64_t b2,
  uint64_t b3,
  uint64_t b4
)
{
  uint64_t b0_ = b0 & (uint64_t )0x7ffffffffffff;
  uint64_t r0 = b0 >> (uint32_t )51;
  uint64_t b1_ = b1 + r0 & (uint64_t )0x7ffffffffffff;
  uint64_t r1 = b1 + r0 >> (uint32_t )51;
  uint64_t b2_ = b2 + r1 & (uint64_t )0x7ffffffffffff;
  uint64_t r2 = b2 + r1 >> (uint32_t )51;
  uint64_t b3_ = b3 + r2 & (uint64_t )0x7ffffffffffff;
  uint64_t r3 = b3 + r2 >> (uint32_t )51;
  uint64_t b4_ = b4 + r3 & (uint64_t )0x7ffffffffffff;
  uint64_t b5_ = b4 + r3 >> (uint32_t )51;
  Hacl_EC_Curve25519_Utils_update_6(b, b0_, b1_, b2_, b3_, b4_, b5_);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_1__(uint64_t *b)
{
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b3 = b[(uint32_t )3];
  uint64_t b4 = b[(uint32_t )4];
  Hacl_EC_Curve25519_Bignum_Modulo_carry_1_0_(b, b0, b1, b2, b3, b4);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_1_(uint64_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_carry_1__(b);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_2__(uint64_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_carry_1__(b);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_2_(uint64_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_carry_2__(b);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_top__(uint64_t *b)
{
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b5 = b[(uint32_t )5];
  b[(uint32_t )0] = b0 + b5 + (b5 << (uint32_t )4) + (b5 << (uint32_t )1);
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_top_1_(uint64_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_carry_top__(b);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_top_2_(uint64_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_carry_top__(b);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_0_to_1__(uint64_t *b)
{
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t b0_ = b0 & (uint64_t )0x7ffffffffffff;
  uint64_t r0 = b0 >> (uint32_t )51;
  b[(uint32_t )0] = b0_;
  b[(uint32_t )1] = b1 + r0;
}

void Hacl_EC_Curve25519_Bignum_Modulo_carry_0_to_1_(uint64_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_carry_0_to_1__(b);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_freduce_coefficients(uint64_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_carry_1_(b);
  Hacl_EC_Curve25519_Bignum_Modulo_carry_top_1_(b);
  Hacl_EC_Curve25519_Bignum_Modulo_carry_2_(b);
  Hacl_EC_Curve25519_Bignum_Modulo_carry_top_2_(b);
  Hacl_EC_Curve25519_Bignum_Modulo_carry_0_to_1_(b);
  return;
}

void Hacl_EC_Curve25519_Bignum_Modulo_normalize(uint64_t *b)
{
  uint64_t two51m1 = (uint64_t )0x7ffffffffffff;
  uint64_t two51m19 = (uint64_t )0x7ffffffffffed;
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b3 = b[(uint32_t )3];
  uint64_t b4 = b[(uint32_t )4];
  uint64_t mask = FStar_UInt64_eq_mask(b4, two51m1);
  uint64_t mask4 = FStar_UInt64_eq_mask(b4, two51m1);
  uint64_t mask3 = FStar_UInt64_eq_mask(b3, two51m1);
  uint64_t mask2 = FStar_UInt64_eq_mask(b2, two51m1);
  uint64_t mask1 = FStar_UInt64_eq_mask(b1, two51m1);
  uint64_t mask0 = FStar_UInt64_gte_mask(b0, two51m19);
  uint64_t mask5 = mask4 & mask3 & mask2 & mask1 & mask0;
  uint64_t b0_ = b0 - (two51m19 & mask5);
  uint64_t b1_ = b1 - (b1 & mask5);
  uint64_t b2_ = b2 - (b2 & mask5);
  uint64_t b3_ = b3 - (b3 & mask5);
  uint64_t b4_ = b4 - (b4 & mask5);
  b[(uint32_t )0] = b0_;
  b[(uint32_t )1] = b1_;
  b[(uint32_t )2] = b2_;
  b[(uint32_t )3] = b3_;
  b[(uint32_t )4] = b4_;
}

