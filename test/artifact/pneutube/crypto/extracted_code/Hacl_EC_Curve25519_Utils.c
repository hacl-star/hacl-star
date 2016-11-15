#include "Hacl_EC_Curve25519_Utils.h"

void
Hacl_EC_Curve25519_Utils_update_5(
  uint64_t *c,
  uint64_t c0,
  uint64_t c1,
  uint64_t c2,
  uint64_t c3,
  uint64_t c4
)
{
  c[(uint32_t )0] = c0;
  c[(uint32_t )1] = c1;
  c[(uint32_t )2] = c2;
  c[(uint32_t )3] = c3;
  c[(uint32_t )4] = c4;
}

void
Hacl_EC_Curve25519_Utils_update_6(
  uint64_t *c,
  uint64_t c0,
  uint64_t c1,
  uint64_t c2,
  uint64_t c3,
  uint64_t c4,
  uint64_t c5
)
{
  c[(uint32_t )0] = c0;
  c[(uint32_t )1] = c1;
  c[(uint32_t )2] = c2;
  c[(uint32_t )3] = c3;
  c[(uint32_t )4] = c4;
  c[(uint32_t )5] = c5;
}

void
Hacl_EC_Curve25519_Utils_update_9(
  uint64_t *c,
  uint64_t c0,
  uint64_t c1,
  uint64_t c2,
  uint64_t c3,
  uint64_t c4,
  uint64_t c5,
  uint64_t c6,
  uint64_t c7,
  uint64_t c8
)
{
  c[(uint32_t )0] = c0;
  c[(uint32_t )1] = c1;
  c[(uint32_t )2] = c2;
  c[(uint32_t )3] = c3;
  c[(uint32_t )4] = c4;
  c[(uint32_t )5] = c5;
  c[(uint32_t )6] = c6;
  c[(uint32_t )7] = c7;
  c[(uint32_t )8] = c8;
}

void
Hacl_EC_Curve25519_Utils_update_wide_5(
  FStar_UInt128_t *c,
  FStar_UInt128_t c0,
  FStar_UInt128_t c1,
  FStar_UInt128_t c2,
  FStar_UInt128_t c3,
  FStar_UInt128_t c4
)
{
  c[(uint32_t )0] = c0;
  c[(uint32_t )1] = c1;
  c[(uint32_t )2] = c2;
  c[(uint32_t )3] = c3;
  c[(uint32_t )4] = c4;
}

void
Hacl_EC_Curve25519_Utils_update_wide_6(
  FStar_UInt128_t *c,
  FStar_UInt128_t c0,
  FStar_UInt128_t c1,
  FStar_UInt128_t c2,
  FStar_UInt128_t c3,
  FStar_UInt128_t c4,
  FStar_UInt128_t c5
)
{
  c[(uint32_t )0] = c0;
  c[(uint32_t )1] = c1;
  c[(uint32_t )2] = c2;
  c[(uint32_t )3] = c3;
  c[(uint32_t )4] = c4;
  c[(uint32_t )5] = c5;
}

void
Hacl_EC_Curve25519_Utils_update_wide_9(
  FStar_UInt128_t *c,
  FStar_UInt128_t c0,
  FStar_UInt128_t c1,
  FStar_UInt128_t c2,
  FStar_UInt128_t c3,
  FStar_UInt128_t c4,
  FStar_UInt128_t c5,
  FStar_UInt128_t c6,
  FStar_UInt128_t c7,
  FStar_UInt128_t c8
)
{
  c[(uint32_t )0] = c0;
  c[(uint32_t )1] = c1;
  c[(uint32_t )2] = c2;
  c[(uint32_t )3] = c3;
  c[(uint32_t )4] = c4;
  c[(uint32_t )5] = c5;
  c[(uint32_t )6] = c6;
  c[(uint32_t )7] = c7;
  c[(uint32_t )8] = c8;
}

