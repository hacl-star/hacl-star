#include "Hacl_EC_Curve25519_Bignum.h"

void Hacl_EC_Curve25519_Bignum_copy_bigint(uint64_t *output, uint64_t *i)
{
  uint64_t i0 = i[(uint32_t )0];
  uint64_t i1 = i[(uint32_t )1];
  uint64_t i2 = i[(uint32_t )2];
  uint64_t i3 = i[(uint32_t )3];
  uint64_t i4 = i[(uint32_t )4];
  Hacl_EC_Curve25519_Utils_update_5(output, i0, i1, i2, i3, i4);
  return;
}

void Hacl_EC_Curve25519_Bignum_copy_to_bigint_(uint64_t *output, FStar_UInt128_t *b)
{
  FStar_UInt128_t b0 = b[(uint32_t )0];
  FStar_UInt128_t b1 = b[(uint32_t )1];
  FStar_UInt128_t b2 = b[(uint32_t )2];
  FStar_UInt128_t b3 = b[(uint32_t )3];
  FStar_UInt128_t b4 = b[(uint32_t )4];
  Hacl_EC_Curve25519_Utils_update_5(output,
    FStar_Int_Cast_uint128_to_uint64(b0),
    FStar_Int_Cast_uint128_to_uint64(b1),
    FStar_Int_Cast_uint128_to_uint64(b2),
    FStar_Int_Cast_uint128_to_uint64(b3),
    FStar_Int_Cast_uint128_to_uint64(b4));
  return;
}

void Hacl_EC_Curve25519_Bignum_copy_to_bigint(uint64_t *output, FStar_UInt128_t *b)
{
  Hacl_EC_Curve25519_Bignum_copy_to_bigint_(output, b);
  return;
}

void Hacl_EC_Curve25519_Bignum_copy_to_bigint_wide_(FStar_UInt128_t *output, uint64_t *b)
{
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b3 = b[(uint32_t )3];
  uint64_t b4 = b[(uint32_t )4];
  Hacl_EC_Curve25519_Utils_update_wide_5(output,
    FStar_Int_Cast_uint64_to_uint128(b0),
    FStar_Int_Cast_uint64_to_uint128(b1),
    FStar_Int_Cast_uint64_to_uint128(b2),
    FStar_Int_Cast_uint64_to_uint128(b3),
    FStar_Int_Cast_uint64_to_uint128(b4));
  return;
}

void Hacl_EC_Curve25519_Bignum_copy_to_bigint_wide(FStar_UInt128_t *output, uint64_t *b)
{
  Hacl_EC_Curve25519_Bignum_copy_to_bigint_wide_(output, b);
  return;
}

void Hacl_EC_Curve25519_Bignum_modulo(uint64_t *output, FStar_UInt128_t *b)
{
  Hacl_EC_Curve25519_Bignum_Modulo_freduce_degree(b);
  Hacl_EC_Curve25519_Bignum_Modulo_freduce_coefficients_wide(b);
  Hacl_EC_Curve25519_Bignum_copy_to_bigint(output, b);
  return;
}

void Hacl_EC_Curve25519_Bignum_fsum(uint64_t *a, uint64_t *b)
{
  Hacl_EC_Curve25519_Bignum_Fsum_fsum_0(a, b);
  Hacl_EC_Curve25519_Bignum_Modulo_freduce_coefficients(a);
  return;
}

void Hacl_EC_Curve25519_Bignum_fdifference(uint64_t *a, uint64_t *b)
{
  uint64_t b_[Hacl_EC_Curve25519_Parameters_nlength];
  memset(b_, 0, Hacl_EC_Curve25519_Parameters_nlength * sizeof b_[0]);
  Hacl_EC_Curve25519_Bignum_copy_bigint(b_, b);
  Hacl_EC_Curve25519_Bignum_Fdifference_add_big_zero(b_);
  Hacl_EC_Curve25519_Bignum_Fdifference_fdifference_0(a, b_);
  Hacl_EC_Curve25519_Bignum_Modulo_freduce_coefficients(a);
}

void Hacl_EC_Curve25519_Bignum_fscalar(uint64_t *res, uint64_t *b, uint64_t s)
{
  FStar_UInt128_t tmp[6];
  for (uintmax_t i = 0; i < (uint32_t )6; ++i)
    tmp[i] = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);
  Hacl_EC_Curve25519_Bignum_Fscalar_scalar_(tmp, b, s);
  Hacl_EC_Curve25519_Bignum_Modulo_freduce_coefficients_wide(tmp);
  Hacl_EC_Curve25519_Bignum_copy_to_bigint(res, tmp);
}

void Hacl_EC_Curve25519_Bignum_fmul(uint64_t *res, uint64_t *a, uint64_t *b)
{
  FStar_UInt128_t tmp[9];
  for (uintmax_t i = 0; i < (uint32_t )9; ++i)
    tmp[i] = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);
  Hacl_EC_Curve25519_Bignum_Fproduct_multiplication(tmp, a, b);
  Hacl_EC_Curve25519_Bignum_modulo(res, tmp);
}

void Hacl_EC_Curve25519_Bignum_fsquare(uint64_t *res, uint64_t *a)
{
  Hacl_EC_Curve25519_Bignum_fmul(res, a, a);
  return;
}

