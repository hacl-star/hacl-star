#include "Hacl_EC_Curve25519_Bignum_Fscalar.h"

void Hacl_EC_Curve25519_Bignum_Fscalar_fscalar_(FStar_UInt128_t *res, uint64_t *a, uint64_t s)
{
  uint64_t a0 = a[(uint32_t )0];
  uint64_t a1 = a[(uint32_t )1];
  uint64_t a2 = a[(uint32_t )2];
  uint64_t a3 = a[(uint32_t )3];
  uint64_t a4 = a[(uint32_t )4];
  FStar_UInt128_t r0 = FStar_UInt128_mul_wide(a0, s);
  FStar_UInt128_t r1 = FStar_UInt128_mul_wide(a1, s);
  FStar_UInt128_t r2 = FStar_UInt128_mul_wide(a2, s);
  FStar_UInt128_t r3 = FStar_UInt128_mul_wide(a3, s);
  FStar_UInt128_t r4 = FStar_UInt128_mul_wide(a4, s);
  Hacl_EC_Curve25519_Utils_update_wide_5(res, r0, r1, r2, r3, r4);
  return;
}

void Hacl_EC_Curve25519_Bignum_Fscalar_scalar_(FStar_UInt128_t *res, uint64_t *a, uint64_t s)
{
  Hacl_EC_Curve25519_Bignum_Fscalar_fscalar_(res, a, s);
  return;
}

