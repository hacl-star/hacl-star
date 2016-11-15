#include "Hacl_EC_Curve25519_Bignum_Fdifference.h"

void Hacl_EC_Curve25519_Bignum_Fdifference_add_big_zero_(uint64_t *b)
{
  uint64_t two52m38 = (uint64_t )0xfffffffffffda;
  uint64_t two52m2 = (uint64_t )0xffffffffffffe;
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b3 = b[(uint32_t )3];
  uint64_t b4 = b[(uint32_t )4];
  uint64_t c0 = b0 + two52m38;
  uint64_t c1 = b1 + two52m2;
  uint64_t c2 = b2 + two52m2;
  uint64_t c3 = b3 + two52m2;
  uint64_t c4 = b4 + two52m2;
  Hacl_EC_Curve25519_Utils_update_5(b, c0, c1, c2, c3, c4);
  return;
}

void Hacl_EC_Curve25519_Bignum_Fdifference_add_big_zero(uint64_t *b)
{
  Hacl_EC_Curve25519_Bignum_Fdifference_add_big_zero_(b);
  return;
}

void Hacl_EC_Curve25519_Bignum_Fdifference_fdifference_(uint64_t *a, uint64_t *b)
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
  uint64_t c0 = b0 - a0;
  uint64_t c1 = b1 - a1;
  uint64_t c2 = b2 - a2;
  uint64_t c3 = b3 - a3;
  uint64_t c4 = b4 - a4;
  Hacl_EC_Curve25519_Utils_update_5(a, c0, c1, c2, c3, c4);
  return;
}

void Hacl_EC_Curve25519_Bignum_Fdifference_fdifference_0(uint64_t *a, uint64_t *b)
{
  Hacl_EC_Curve25519_Bignum_Fdifference_fdifference_(a, b);
  return;
}

