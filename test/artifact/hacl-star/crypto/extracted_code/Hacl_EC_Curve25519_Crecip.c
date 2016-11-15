#include "Hacl_EC_Curve25519_Crecip.h"

void Hacl_EC_Curve25519_Crecip_loop(uint64_t *tmp, uint64_t *v, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    Hacl_EC_Curve25519_Bignum_fsquare(tmp, v);
    Hacl_EC_Curve25519_Bignum_fsquare(v, tmp);
    Hacl_EC_Curve25519_Crecip_loop(tmp, v, ctr - (uint32_t )1);
    return;
  }
}

void Hacl_EC_Curve25519_Crecip_crecip_0(uint64_t *tmp, uint64_t *z)
{
  uint64_t *z2 = tmp + (uint32_t )0;
  uint64_t *z9 = tmp + (uint32_t )5;
  uint64_t *z11 = tmp + (uint32_t )10;
  uint64_t *z2_5_0 = tmp + (uint32_t )15;
  uint64_t *t0 = tmp + (uint32_t )40;
  uint64_t *t1 = tmp + (uint32_t )45;
  Hacl_EC_Curve25519_Bignum_fsquare(z2, z);
  Hacl_EC_Curve25519_Bignum_fsquare(t1, z2);
  Hacl_EC_Curve25519_Bignum_fsquare(t0, t1);
  Hacl_EC_Curve25519_Bignum_fmul(z9, t0, z);
  Hacl_EC_Curve25519_Bignum_fmul(z11, z9, z2);
  Hacl_EC_Curve25519_Bignum_fsquare(t0, z11);
  Hacl_EC_Curve25519_Bignum_fmul(z2_5_0, t0, z9);
  return;
}

void Hacl_EC_Curve25519_Crecip_crecip_1(uint64_t *tmp, uint64_t *z)
{
  uint64_t *z2_5_0 = tmp + (uint32_t )15;
  uint64_t *z2_10_0 = tmp + (uint32_t )20;
  uint64_t *t0 = tmp + (uint32_t )40;
  uint64_t *t1 = tmp + (uint32_t )45;
  Hacl_EC_Curve25519_Bignum_fsquare(t0, z2_5_0);
  Hacl_EC_Curve25519_Bignum_fsquare(t1, t0);
  Hacl_EC_Curve25519_Bignum_fsquare(t0, t1);
  Hacl_EC_Curve25519_Bignum_fsquare(t1, t0);
  Hacl_EC_Curve25519_Bignum_fsquare(t0, t1);
  Hacl_EC_Curve25519_Bignum_fmul(z2_10_0, t0, z2_5_0);
  return;
}

void Hacl_EC_Curve25519_Crecip_crecip_2(uint64_t *tmp, uint64_t *z)
{
  uint64_t *z2_10_0 = tmp + (uint32_t )20;
  uint64_t *z2_20_0 = tmp + (uint32_t )25;
  uint64_t *z2_50_0 = tmp + (uint32_t )30;
  uint64_t *t0 = tmp + (uint32_t )40;
  uint64_t *t1 = tmp + (uint32_t )45;
  Hacl_EC_Curve25519_Bignum_fsquare(t0, z2_10_0);
  Hacl_EC_Curve25519_Bignum_fsquare(t1, t0);
  Hacl_EC_Curve25519_Crecip_loop(t0, t1, (uint32_t )4);
  Hacl_EC_Curve25519_Bignum_fmul(z2_20_0, t1, z2_10_0);
  Hacl_EC_Curve25519_Bignum_fsquare(t0, z2_20_0);
  Hacl_EC_Curve25519_Bignum_fsquare(t1, t0);
  Hacl_EC_Curve25519_Crecip_loop(t0, t1, (uint32_t )9);
  Hacl_EC_Curve25519_Bignum_fmul(t0, t1, z2_20_0);
  Hacl_EC_Curve25519_Bignum_fsquare(t1, t0);
  Hacl_EC_Curve25519_Bignum_fsquare(t0, t1);
  Hacl_EC_Curve25519_Crecip_loop(t1, t0, (uint32_t )4);
  Hacl_EC_Curve25519_Bignum_fmul(z2_50_0, t0, z2_10_0);
  return;
}

void Hacl_EC_Curve25519_Crecip_crecip_3(uint64_t *tmp, uint64_t *z)
{
  uint64_t *z2_50_0 = tmp + (uint32_t )30;
  uint64_t *z2_100_0 = tmp + (uint32_t )35;
  uint64_t *t0 = tmp + (uint32_t )40;
  uint64_t *t1 = tmp + (uint32_t )45;
  Hacl_EC_Curve25519_Bignum_fsquare(t0, z2_50_0);
  Hacl_EC_Curve25519_Bignum_fsquare(t1, t0);
  Hacl_EC_Curve25519_Crecip_loop(t0, t1, (uint32_t )24);
  Hacl_EC_Curve25519_Bignum_fmul(z2_100_0, t1, z2_50_0);
  Hacl_EC_Curve25519_Bignum_fsquare(t1, z2_100_0);
  Hacl_EC_Curve25519_Bignum_fsquare(t0, t1);
  Hacl_EC_Curve25519_Crecip_loop(t1, t0, (uint32_t )49);
  Hacl_EC_Curve25519_Bignum_fmul(t1, t0, z2_100_0);
  return;
}

void Hacl_EC_Curve25519_Crecip_crecip_4(uint64_t *tmp, uint64_t *z)
{
  uint64_t *z2_50_0 = tmp + (uint32_t )30;
  uint64_t *t0 = tmp + (uint32_t )40;
  uint64_t *t1 = tmp + (uint32_t )45;
  Hacl_EC_Curve25519_Bignum_fsquare(t0, t1);
  Hacl_EC_Curve25519_Bignum_fsquare(t1, t0);
  Hacl_EC_Curve25519_Crecip_loop(t0, t1, (uint32_t )24);
  Hacl_EC_Curve25519_Bignum_fmul(t0, t1, z2_50_0);
  Hacl_EC_Curve25519_Bignum_fsquare(t1, t0);
  Hacl_EC_Curve25519_Bignum_fsquare(t0, t1);
  Hacl_EC_Curve25519_Bignum_fsquare(t1, t0);
  Hacl_EC_Curve25519_Bignum_fsquare(t0, t1);
  Hacl_EC_Curve25519_Bignum_fsquare(t1, t0);
  return;
}

void Hacl_EC_Curve25519_Crecip_crecip_(uint64_t *output, uint64_t *z)
{
  uint64_t tmp[(uint32_t )10 * Hacl_EC_Curve25519_Parameters_nlength];
  memset(tmp, 0, (uint32_t )10 * Hacl_EC_Curve25519_Parameters_nlength * sizeof tmp[0]);
  uint64_t *z2 = tmp + (uint32_t )0;
  uint64_t *z9 = tmp + (uint32_t )5;
  uint64_t *z11 = tmp + (uint32_t )10;
  uint64_t *z2_5_0 = tmp + (uint32_t )15;
  uint64_t *z2_10_0 = tmp + (uint32_t )20;
  uint64_t *z2_20_0 = tmp + (uint32_t )25;
  uint64_t *z2_50_0 = tmp + (uint32_t )30;
  uint64_t *z2_100_0 = tmp + (uint32_t )35;
  uint64_t *t0 = tmp + (uint32_t )40;
  uint64_t *t1 = tmp + (uint32_t )45;
  Hacl_EC_Curve25519_Crecip_crecip_0(tmp, z);
  Hacl_EC_Curve25519_Crecip_crecip_1(tmp, z);
  Hacl_EC_Curve25519_Crecip_crecip_2(tmp, z);
  Hacl_EC_Curve25519_Crecip_crecip_3(tmp, z);
  Hacl_EC_Curve25519_Crecip_crecip_4(tmp, z);
  Hacl_EC_Curve25519_Bignum_fmul(output, t1, z11);
}

