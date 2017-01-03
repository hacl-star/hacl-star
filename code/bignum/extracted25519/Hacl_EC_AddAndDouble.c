#include "Hacl_EC_AddAndDouble.h"

void
Hacl_EC_AddAndDouble_fmonty(
  uint64_t *pp,
  uint64_t *ppq,
  uint64_t *p,
  uint64_t *pq,
  uint64_t *qmqp
)
{
  uint64_t *qx = Hacl_EC_Point_getx(qmqp);
  uint64_t *x2 = Hacl_EC_Point_getx(pp);
  uint64_t *z2 = Hacl_EC_Point_getz(pp);
  uint64_t *x3 = Hacl_EC_Point_getx(ppq);
  uint64_t *z3 = Hacl_EC_Point_getz(ppq);
  uint64_t *x = Hacl_EC_Point_getx(p);
  uint64_t *z = Hacl_EC_Point_getz(p);
  uint64_t *xprime = Hacl_EC_Point_getx(pq);
  uint64_t *zprime = Hacl_EC_Point_getz(pq);
  uint64_t buf[40] = { 0 };
  uint64_t *origx = buf + (uint32_t )0;
  uint64_t *origxprime = buf + (uint32_t )5;
  uint64_t *zzz = buf + (uint32_t )10;
  uint64_t *xx = buf + (uint32_t )15;
  uint64_t *zz = buf + (uint32_t )20;
  uint64_t *xxprime = buf + (uint32_t )25;
  uint64_t *zzprime = buf + (uint32_t )30;
  uint64_t *zzzprime = buf + (uint32_t )35;
  memcpy(origx, x, (uint32_t )5 * sizeof x[0]);
  Hacl_Bignum_fsum(x, z);
  Hacl_Bignum_fdifference(z, origx);
  memcpy(origxprime, xprime, (uint32_t )5 * sizeof xprime[0]);
  Hacl_Bignum_fsum(xprime, zprime);
  Hacl_Bignum_fdifference(zprime, origxprime);
  Hacl_Bignum_fmul(xxprime, xprime, z);
  Hacl_Bignum_fmul(zzprime, x, zprime);
  memcpy(origxprime, xxprime, (uint32_t )5 * sizeof xxprime[0]);
  Hacl_Bignum_fsum(xxprime, zzprime);
  Hacl_Bignum_fdifference(zzprime, origxprime);
  Hacl_Bignum_fsquare_times(x3, xxprime, (uint32_t )1);
  Hacl_Bignum_fsquare_times(zzzprime, zzprime, (uint32_t )1);
  Hacl_Bignum_fmul(z3, zzzprime, qx);
  Hacl_Bignum_fsquare_times(xx, x, (uint32_t )1);
  Hacl_Bignum_fsquare_times(zz, z, (uint32_t )1);
  Hacl_Bignum_fmul(x2, xx, zz);
  Hacl_Bignum_fdifference(zz, xx);
  Hacl_Bignum_fscalar(zzz, zz, (uint64_t )121665);
  Hacl_Bignum_fsum(zzz, xx);
  Hacl_Bignum_fmul(z2, zz, zzz);
}

