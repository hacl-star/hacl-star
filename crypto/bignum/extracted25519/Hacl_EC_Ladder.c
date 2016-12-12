#include "Hacl_EC_Ladder.h"

void
Hacl_EC_Ladder_cmult_small_loop(
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint8_t byt,
  uint32_t i
)
{
  uint64_t *nqx = Hacl_EC_Point_getx(nq);
  uint64_t *nqz = Hacl_EC_Point_getz(nq);
  uint64_t *nqpqx = Hacl_EC_Point_getx(nqpq);
  uint64_t *nqpqz = Hacl_EC_Point_getz(nqpq);
  uint64_t *nqx2 = Hacl_EC_Point_getx(nq2);
  uint64_t *nqz2 = Hacl_EC_Point_getz(nq2);
  uint64_t *nqpqx2 = Hacl_EC_Point_getx(nqpq2);
  uint64_t *nqpqz2 = Hacl_EC_Point_getz(nqpq2);
  if (i == (uint32_t )0)
    return;
  else
  {
    uint64_t bit = (uint64_t )(byt >> (uint32_t )7);
    Hacl_EC_Point_swap_conditional(nq, nqpq, bit);
    Hacl_EC_AddAndDouble_fmonty(nq2, nqpq2, nq, nqpq, q);
    Hacl_EC_Point_swap_conditional(nq2, nqpq2, bit);
    uint64_t *t0 = nq;
    uint64_t *nq = nq2;
    uint64_t *nq2 = t0;
    uint64_t *t = nqpq;
    uint64_t *nqpq = nqpq2;
    uint64_t *nqpq2 = t;
    uint8_t byt0 = byt << (uint32_t )1;
    Hacl_EC_Ladder_cmult_small_loop(nq, nqpq, nq2, nqpq2, q, byt0, i - (uint32_t )1);
    return;
  }
}

void
Hacl_EC_Ladder_cmult_big_loop(
  uint8_t *n,
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint32_t i
)
{
  if (i == (uint32_t )0)
    return;
  else
  {
    uint32_t i0 = i - (uint32_t )1;
    uint8_t byte = n[i0];
    Hacl_EC_Ladder_cmult_small_loop(nq, nqpq, nq2, nqpq2, q, byte, (uint32_t )8);
    Hacl_EC_Ladder_cmult_big_loop(n, nq, nqpq, nq2, nqpq2, q, i0);
    return;
  }
}

void Hacl_EC_Ladder_cmult(uint64_t *result, uint8_t *n, uint64_t *q)
{
  uint64_t *nq = result;
  uint64_t buf0[10] = { 0 };
  uint64_t
  *nqpq = Hacl_EC_Point_make(buf0 + (uint32_t )0, buf0 + (uint32_t )0, buf0 + (uint32_t )5);
  uint64_t buf1[10] = { 0 };
  uint64_t
  *nqpq2 = Hacl_EC_Point_make(buf1 + (uint32_t )0, buf1 + (uint32_t )0, buf1 + (uint32_t )5);
  uint64_t buf[10] = { 0 };
  uint64_t *nq2 = Hacl_EC_Point_make(buf + (uint32_t )0, buf + (uint32_t )0, buf + (uint32_t )5);
  Hacl_EC_Point_copy(nqpq, q);
  Hacl_EC_Ladder_cmult_big_loop(n, nq, nqpq, nq2, nqpq2, q, (uint32_t )32);
  Hacl_EC_Point_copy(result, nq);
}

