#include "Hacl_EC_Curve25519_Bignum_Fproduct.h"

void
Hacl_EC_Curve25519_Bignum_Fproduct_multiplication_0(
  FStar_UInt128_t *c,
  uint64_t a0,
  uint64_t a1,
  uint64_t a2,
  uint64_t a3,
  uint64_t a4,
  uint64_t b0,
  uint64_t b1,
  uint64_t b2,
  uint64_t b3,
  uint64_t b4
)
{
  FStar_UInt128_t ab00 = FStar_UInt128_mul_wide(a0, b0);
  FStar_UInt128_t ab01 = FStar_UInt128_mul_wide(a0, b1);
  FStar_UInt128_t ab02 = FStar_UInt128_mul_wide(a0, b2);
  FStar_UInt128_t ab03 = FStar_UInt128_mul_wide(a0, b3);
  FStar_UInt128_t ab04 = FStar_UInt128_mul_wide(a0, b4);
  FStar_UInt128_t ab10 = FStar_UInt128_mul_wide(a1, b0);
  FStar_UInt128_t ab11 = FStar_UInt128_mul_wide(a1, b1);
  FStar_UInt128_t ab12 = FStar_UInt128_mul_wide(a1, b2);
  FStar_UInt128_t ab13 = FStar_UInt128_mul_wide(a1, b3);
  FStar_UInt128_t ab14 = FStar_UInt128_mul_wide(a1, b4);
  FStar_UInt128_t ab20 = FStar_UInt128_mul_wide(a2, b0);
  FStar_UInt128_t ab21 = FStar_UInt128_mul_wide(a2, b1);
  FStar_UInt128_t ab22 = FStar_UInt128_mul_wide(a2, b2);
  FStar_UInt128_t ab23 = FStar_UInt128_mul_wide(a2, b3);
  FStar_UInt128_t ab24 = FStar_UInt128_mul_wide(a2, b4);
  FStar_UInt128_t ab30 = FStar_UInt128_mul_wide(a3, b0);
  FStar_UInt128_t ab31 = FStar_UInt128_mul_wide(a3, b1);
  FStar_UInt128_t ab32 = FStar_UInt128_mul_wide(a3, b2);
  FStar_UInt128_t ab33 = FStar_UInt128_mul_wide(a3, b3);
  FStar_UInt128_t ab34 = FStar_UInt128_mul_wide(a3, b4);
  FStar_UInt128_t ab40 = FStar_UInt128_mul_wide(a4, b0);
  FStar_UInt128_t ab41 = FStar_UInt128_mul_wide(a4, b1);
  FStar_UInt128_t ab42 = FStar_UInt128_mul_wide(a4, b2);
  FStar_UInt128_t ab43 = FStar_UInt128_mul_wide(a4, b3);
  FStar_UInt128_t ab44 = FStar_UInt128_mul_wide(a4, b4);
  FStar_UInt128_t c0 = ab00;
  FStar_UInt128_t c1 = FStar_UInt128_add_mod(ab01, ab10);
  FStar_UInt128_t c2 = FStar_UInt128_add_mod(FStar_UInt128_add_mod(ab02, ab11), ab20);
  FStar_UInt128_t
  c3 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(ab03, ab12), ab21),
      ab30);
  FStar_UInt128_t
  c4 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(ab04,
            ab13),
          ab22),
        ab31),
      ab40);
  FStar_UInt128_t
  c5 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(ab14, ab23), ab32),
      ab41);
  FStar_UInt128_t c6 = FStar_UInt128_add_mod(FStar_UInt128_add_mod(ab24, ab33), ab42);
  FStar_UInt128_t c7 = FStar_UInt128_add_mod(ab34, ab43);
  FStar_UInt128_t c8 = ab44;
  Hacl_EC_Curve25519_Utils_update_wide_9(c, c0, c1, c2, c3, c4, c5, c6, c7, c8);
  return;
}

void
Hacl_EC_Curve25519_Bignum_Fproduct_multiplication_(
  FStar_UInt128_t *c,
  uint64_t *a,
  uint64_t *b
)
{
  uint64_t a0 = a[(uint32_t )0];
  uint64_t a1 = a[(uint32_t )1];
  uint64_t a2 = a[(uint32_t )2];
  uint64_t a3 = a[(uint32_t )3];
  uint64_t a4 = a[(uint32_t )4];
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b3 = b[(uint32_t )3];
  uint64_t b4 = b[(uint32_t )4];
  Hacl_EC_Curve25519_Bignum_Fproduct_multiplication_0(c, a0, a1, a2, a3, a4, b0, b1, b2, b3, b4);
  return;
}

void
Hacl_EC_Curve25519_Bignum_Fproduct_multiplication(FStar_UInt128_t *c, uint64_t *a, uint64_t *b)
{
  Hacl_EC_Curve25519_Bignum_Fproduct_multiplication_(c, a, b);
  return;
}

