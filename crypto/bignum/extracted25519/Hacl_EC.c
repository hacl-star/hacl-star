#include "Hacl_EC.h"

void Hacl_EC_crypto_scalarmult(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint)
{
  uint64_t buf0[10] = { 0 };
  uint64_t *x0 = buf0 + (uint32_t )0;
  uint64_t *y0 = buf0 + (uint32_t )0;
  uint64_t *z0 = buf0 + (uint32_t )5;
  uint64_t *p = Hacl_EC_Point_make(x0, y0, z0);
  Hacl_EC_Format_fexpand(x0, basepoint);
  z0[(uint32_t )0] = (uint64_t )1;
  uint64_t *q = p;
  uint64_t buf[10] = { 0 };
  uint64_t *x1 = buf + (uint32_t )0;
  uint64_t *y = buf + (uint32_t )0;
  uint64_t *z = buf + (uint32_t )5;
  x1[(uint32_t )0] = (uint64_t )1;
  uint64_t *p0 = Hacl_EC_Point_make(x1, y, z);
  uint64_t *nq = p0;
  uint64_t *x = Hacl_EC_Point_getx(nq);
  uint64_t *z1 = Hacl_EC_Point_getz(nq);
  uint64_t zmone[5] = { 0 };
  uint8_t e[32] = { 0 };
  memcpy(e, secret, (uint32_t )32 * sizeof secret[0]);
  uint8_t e00 = e[(uint32_t )0];
  uint8_t e310 = e[(uint32_t )31];
  uint8_t e0 = e00 & (uint8_t )248;
  uint8_t e31 = e310 & (uint8_t )127;
  uint8_t e311 = e31 | (uint8_t )64;
  e[(uint32_t )0] = e0;
  e[(uint32_t )31] = e311;
  uint8_t *scalar = e;
  Hacl_EC_Ladder_cmult(nq, scalar, q);
  Hacl_EC_Format_scalar_of_point(mypublic, nq);
}

