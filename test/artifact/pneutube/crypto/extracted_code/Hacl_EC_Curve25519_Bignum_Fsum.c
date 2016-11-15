#include "Hacl_EC_Curve25519_Bignum_Fsum.h"

void Hacl_EC_Curve25519_Bignum_Fsum_fsum_(uint64_t *a, uint64_t *b)
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
  uint64_t ab0 = a0 + b0;
  uint64_t ab1 = a1 + b1;
  uint64_t ab2 = a2 + b2;
  uint64_t ab3 = a3 + b3;
  uint64_t ab4 = a4 + b4;
  Hacl_EC_Curve25519_Utils_update_5(a, ab0, ab1, ab2, ab3, ab4);
  return;
}

void Hacl_EC_Curve25519_Bignum_Fsum_fsum_0(uint64_t *a, uint64_t *b)
{
  Hacl_EC_Curve25519_Bignum_Fsum_fsum_(a, b);
  return;
}

