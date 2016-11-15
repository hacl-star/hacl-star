#include "Hacl_EC_Curve25519_AddAndDouble.h"

void
Hacl_EC_Curve25519_AddAndDouble_double_and_add_0(
  Hacl_EC_Curve25519_PPoint_point pp,
  Hacl_EC_Curve25519_PPoint_point ppq,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point p_plus_q,
  Hacl_EC_Curve25519_PPoint_point q,
  uint64_t *tmp
)
{
  uint64_t *x = Hacl_EC_Curve25519_PPoint_get_x(p);
  uint64_t *xprime = Hacl_EC_Curve25519_PPoint_get_x(p_plus_q);
  uint64_t *origx = tmp + (uint32_t )0;
  uint64_t *origxprime = tmp + (uint32_t )6;
  memcpy(origx, x, Hacl_EC_Curve25519_Parameters_nlength * sizeof x[0]);
  memcpy(origxprime, xprime, Hacl_EC_Curve25519_Parameters_nlength * sizeof xprime[0]);
}

void
Hacl_EC_Curve25519_AddAndDouble_lemma_helper_2(
  FStar_HyperHeap_rid r,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  Prims_prop (*sub)(FStar_Heap_aref x0),
  Prims_prop (*s)(FStar_Heap_aref x0)
)
{
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_lemma_helper_3(
  FStar_HyperHeap_rid r,
  Prims_prop (*s)(FStar_Heap_aref x0),
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2,
  FStar_HyperStack_mem h3,
  FStar_HyperStack_mem h4
)
{
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_lemma_helper_1(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2,
  FStar_HyperStack_mem h3,
  FStar_HyperStack_mem h4,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point pq
)
{
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_double_and_add_1(
  Hacl_EC_Curve25519_PPoint_point pp,
  Hacl_EC_Curve25519_PPoint_point ppq,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point p_plus_q,
  Hacl_EC_Curve25519_PPoint_point q,
  uint64_t *tmp
)
{
  uint64_t *x = Hacl_EC_Curve25519_PPoint_get_x(p);
  uint64_t *z = Hacl_EC_Curve25519_PPoint_get_z(p);
  uint64_t *xprime = Hacl_EC_Curve25519_PPoint_get_x(p_plus_q);
  uint64_t *zprime = Hacl_EC_Curve25519_PPoint_get_z(p_plus_q);
  uint64_t *origx = tmp + (uint32_t )0;
  uint64_t *origxprime = tmp + (uint32_t )6;
  Hacl_EC_Curve25519_Bignum_fsum(x, z);
  Hacl_EC_Curve25519_Bignum_fdifference(z, origx);
  Hacl_EC_Curve25519_Bignum_fsum(xprime, zprime);
  Hacl_EC_Curve25519_Bignum_fdifference(zprime, origxprime);
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_lemma_helper_4(
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point p_
)
{
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_lemma_helper_5(Hacl_EC_Curve25519_PPoint_point p, uint64_t *p_)
{
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_double_and_add_2(
  Hacl_EC_Curve25519_PPoint_point pp,
  Hacl_EC_Curve25519_PPoint_point ppq,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point pq,
  Hacl_EC_Curve25519_PPoint_point q,
  uint64_t *tmp
)
{
  uint64_t *qmqp = Hacl_EC_Curve25519_PPoint_get_x(q);
  uint64_t *x = Hacl_EC_Curve25519_PPoint_get_x(p);
  uint64_t *z = Hacl_EC_Curve25519_PPoint_get_z(p);
  uint64_t *xprime = Hacl_EC_Curve25519_PPoint_get_x(pq);
  uint64_t *zprime = Hacl_EC_Curve25519_PPoint_get_z(pq);
  uint32_t nl = Hacl_EC_Curve25519_Parameters_nlength + (uint32_t )1;
  uint32_t nl2 = (uint32_t )2 * Hacl_EC_Curve25519_Parameters_nlength - (uint32_t )1;
  uint64_t *origxprime = tmp + nl;
  uint64_t *xxprime = tmp + nl + nl + nl2 + nl2 + nl2;
  uint64_t *zzprime = tmp + nl + nl + nl2 + nl2 + nl2 + nl2;
  uint64_t *xxxprime = tmp + nl + nl + nl2 + nl2 + nl2 + nl2 + nl2;
  uint64_t *zzzprime = tmp + nl + nl + nl2 + nl2 + nl2 + nl2 + nl2 + nl2;
  Hacl_EC_Curve25519_Bignum_fmul(xxprime, xprime, z);
  Hacl_EC_Curve25519_Bignum_fmul(zzprime, x, zprime);
  memcpy(origxprime, xxprime, Hacl_EC_Curve25519_Parameters_nlength * sizeof xxprime[0]);
  Hacl_EC_Curve25519_Bignum_fsum(xxprime, zzprime);
  Hacl_EC_Curve25519_Bignum_fdifference(zzprime, origxprime);
  Hacl_EC_Curve25519_Bignum_fsquare(xxxprime, xxprime);
  Hacl_EC_Curve25519_Bignum_fsquare(zzzprime, zzprime);
  Hacl_EC_Curve25519_Bignum_fmul(zzprime, zzzprime, qmqp);
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_lemma_helper_6(
  FStar_HyperHeap_rid r,
  Prims_prop (*s)(FStar_Heap_aref x0),
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2
)
{
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_double_and_add_3(
  Hacl_EC_Curve25519_PPoint_point pp,
  Hacl_EC_Curve25519_PPoint_point two_p_plus_q,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point pq,
  Hacl_EC_Curve25519_PPoint_point q,
  uint64_t *tmp
)
{
  uint32_t nl = Hacl_EC_Curve25519_Parameters_nlength + (uint32_t )1;
  uint32_t nl2 = (uint32_t )2 * Hacl_EC_Curve25519_Parameters_nlength - (uint32_t )1;
  uint64_t *zzprime = tmp + nl + nl + nl2 + nl2 + nl2 + nl2;
  uint64_t *xxxprime = tmp + nl + nl + nl2 + nl2 + nl2 + nl2 + nl2;
  memcpy(Hacl_EC_Curve25519_PPoint_get_x(two_p_plus_q),
    xxxprime,
    Hacl_EC_Curve25519_Parameters_nlength * sizeof xxxprime[0]);
  memcpy(Hacl_EC_Curve25519_PPoint_get_z(two_p_plus_q),
    zzprime,
    Hacl_EC_Curve25519_Parameters_nlength * sizeof zzprime[0]);
}

void
Hacl_EC_Curve25519_AddAndDouble_double_and_add_4(
  Hacl_EC_Curve25519_PPoint_point pp,
  Hacl_EC_Curve25519_PPoint_point ppq,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point pq,
  Hacl_EC_Curve25519_PPoint_point q,
  uint64_t *tmp
)
{
  uint32_t nl = Hacl_EC_Curve25519_Parameters_nlength + (uint32_t )1;
  uint32_t nl2 = (uint32_t )2 * Hacl_EC_Curve25519_Parameters_nlength - (uint32_t )1;
  uint64_t *x = Hacl_EC_Curve25519_PPoint_get_x(p);
  uint64_t *z = Hacl_EC_Curve25519_PPoint_get_z(p);
  uint64_t *xx = tmp + nl + nl + nl2;
  uint64_t *zz = tmp + nl + nl + nl2 + nl2;
  Hacl_EC_Curve25519_Bignum_fsquare(xx, x);
  Hacl_EC_Curve25519_Bignum_fsquare(zz, z);
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_double_and_add_5(
  Hacl_EC_Curve25519_PPoint_point pp,
  Hacl_EC_Curve25519_PPoint_point ppq,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point pq,
  Hacl_EC_Curve25519_PPoint_point q,
  uint64_t *tmp
)
{
  uint32_t nl = Hacl_EC_Curve25519_Parameters_nlength + (uint32_t )1;
  uint32_t nl2 = (uint32_t )2 * Hacl_EC_Curve25519_Parameters_nlength - (uint32_t )1;
  uint64_t *zzz = tmp + nl + nl;
  uint64_t *xx = tmp + nl + nl + nl2;
  uint64_t *zz = tmp + nl + nl + nl2 + nl2;
  Hacl_EC_Curve25519_Bignum_fdifference(zz, xx);
  Hacl_EC_Curve25519_Bignum_fscalar(zzz, zz, Hacl_EC_Curve25519_Parameters_a24);
  Hacl_EC_Curve25519_Bignum_fsum(zzz, xx);
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_lemma_helper_x(
  FStar_HyperHeap_rid r,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2,
  FStar_HyperStack_mem h3,
  FStar_HyperStack_mem h4,
  FStar_HyperStack_mem h5,
  FStar_HyperStack_mem h6,
  FStar_HyperStack_mem h7,
  FStar_HyperStack_mem h8
)
{
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_lemma_helper_y(
  FStar_HyperHeap_rid r,
  Prims_prop (*sub)(FStar_Heap_aref x0),
  Prims_prop (*s)(FStar_Heap_aref x0),
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1
)
{
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_lemma_helper_z(
  FStar_HyperHeap_rid r,
  FStar_HyperHeap_rid r_,
  Prims_prop (*s)(FStar_Heap_aref x0),
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1
)
{
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_lemma_helper_w(
  Hacl_EC_Curve25519_PPoint_point pp,
  Hacl_EC_Curve25519_PPoint_point ppq,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point pq
)
{
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_lemma_helper_xx(
  FStar_HyperHeap_rid r,
  Prims_prop (*s)(FStar_Heap_aref x0),
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2,
  FStar_HyperStack_mem h3,
  FStar_HyperStack_mem h4,
  FStar_HyperStack_mem h5,
  FStar_HyperStack_mem h6,
  FStar_HyperStack_mem h7,
  FStar_HyperStack_mem h8
)
{
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_double_and_add_(
  Hacl_EC_Curve25519_PPoint_point pp,
  Hacl_EC_Curve25519_PPoint_point ppq,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point pq,
  Hacl_EC_Curve25519_PPoint_point q,
  uint64_t *tmp
)
{
  uint32_t nl = Hacl_EC_Curve25519_Parameters_nlength + (uint32_t )1;
  uint32_t nl2 = (uint32_t )2 * Hacl_EC_Curve25519_Parameters_nlength - (uint32_t )1;
  uint64_t *zzz = tmp + nl + nl;
  uint64_t *xx = tmp + nl + nl + nl2;
  uint64_t *zz = tmp + nl + nl + nl2 + nl2;
  Hacl_EC_Curve25519_AddAndDouble_double_and_add_0(pp, ppq, p, pq, q, tmp);
  Hacl_EC_Curve25519_AddAndDouble_double_and_add_1(pp, ppq, p, pq, q, tmp);
  Hacl_EC_Curve25519_AddAndDouble_double_and_add_2(pp, ppq, p, pq, q, tmp);
  Hacl_EC_Curve25519_AddAndDouble_double_and_add_3(pp, ppq, p, pq, q, tmp);
  Hacl_EC_Curve25519_AddAndDouble_double_and_add_4(pp, ppq, p, pq, q, tmp);
  Hacl_EC_Curve25519_Bignum_fmul(Hacl_EC_Curve25519_PPoint_get_x(pp), xx, zz);
  Hacl_EC_Curve25519_AddAndDouble_double_and_add_5(pp, ppq, p, pq, q, tmp);
  Hacl_EC_Curve25519_Bignum_fmul(Hacl_EC_Curve25519_PPoint_get_z(pp), zz, zzz);
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_lemma_helper_7(
  FStar_HyperStack_mem hinit,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2,
  FStar_HyperStack_mem hfin,
  FStar_HyperHeap_rid r
)
{
  return;
}

void
Hacl_EC_Curve25519_AddAndDouble_double_and_add(
  Hacl_EC_Curve25519_PPoint_point two_p,
  Hacl_EC_Curve25519_PPoint_point two_p_plus_q,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point p_plus_q,
  Hacl_EC_Curve25519_PPoint_point q
)
{
  uint64_t *qmqp = Hacl_EC_Curve25519_PPoint_get_x(q);
  uint64_t *x = Hacl_EC_Curve25519_PPoint_get_x(p);
  uint64_t *z = Hacl_EC_Curve25519_PPoint_get_z(p);
  uint64_t *xprime = Hacl_EC_Curve25519_PPoint_get_x(p_plus_q);
  uint64_t *zprime = Hacl_EC_Curve25519_PPoint_get_z(p_plus_q);
  uint64_t *x2 = Hacl_EC_Curve25519_PPoint_get_x(two_p);
  uint64_t *z2 = Hacl_EC_Curve25519_PPoint_get_z(two_p);
  uint32_t nl = Hacl_EC_Curve25519_Parameters_nlength + (uint32_t )1;
  uint32_t nl2 = (uint32_t )2 * Hacl_EC_Curve25519_Parameters_nlength - (uint32_t )1;
  uint64_t tmp[nl + nl + nl2 + nl2 + nl2 + nl2 + nl2 + nl2 + nl2];
  memset(tmp, 0, (nl + nl + nl2 + nl2 + nl2 + nl2 + nl2 + nl2 + nl2) * sizeof tmp[0]);
  Hacl_EC_Curve25519_AddAndDouble_double_and_add_(two_p, two_p_plus_q, p, p_plus_q, q, tmp);
}

