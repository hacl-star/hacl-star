#include "Multiplication.h"

K___uint64_t_uint64_t Multiplication_mult64(uint64_t x, uint64_t y)
{
  return
    (
      (K___uint64_t_uint64_t ){
        .fst = (x >> (uint32_t )32)
        * (y >> (uint32_t )32)
        + ((x & (uint64_t )0xffffffff) * (y >> (uint32_t )32) >> (uint32_t )32)
        + ((x >> (uint32_t )32) * (y & (uint64_t )0xffffffff) >> (uint32_t )32)
        +
          (((x & (uint64_t )0xffffffff) * (y & (uint64_t )0xffffffff) >> (uint32_t )32)
          + ((x & (uint64_t )0xffffffff) * (y >> (uint32_t )32) & (uint64_t )0xffffffff)
          + ((x >> (uint32_t )32) * (y & (uint64_t )0xffffffff) & (uint64_t )0xffffffff)
          >> (uint32_t )32),
        .snd = ((x & (uint64_t )0xffffffff) * (y & (uint64_t )0xffffffff) >> (uint32_t )32)
        + ((x & (uint64_t )0xffffffff) * (y >> (uint32_t )32) & (uint64_t )0xffffffff)
        + ((x >> (uint32_t )32) * (y & (uint64_t )0xffffffff) & (uint64_t )0xffffffff)
        << (uint32_t )32
        | (x & (uint64_t )0xffffffff) * (y & (uint64_t )0xffffffff) & (uint64_t )0xffffffff
      }
    );
}

K___uint64_t_uint64_t Multiplication_add64(uint64_t x, uint64_t y)
{
  uint64_t ite;
  if (x + y < x)
    ite = (uint64_t )1;
  else
    ite = (uint64_t )0;
  return ((K___uint64_t_uint64_t ){ .fst = ite, .snd = x + y });
}

void
Multiplication_mult_inner_loop(
  uint32_t aLen,
  uint64_t *a,
  uint64_t *b,
  uint32_t i,
  uint32_t j,
  uint64_t carry,
  uint64_t *res
)
{
  if (j < aLen)
  {
    uint64_t uu____112 = a[j];
    uint64_t uu____113 = b[i];
    K___uint64_t_uint64_t uu____107 = Multiplication_mult64(uu____112, uu____113);
    K___uint64_t_uint64_t scrut = uu____107;
    uint64_t carry1 = scrut.fst;
    uint64_t s1 = scrut.snd;
    uint64_t uu____121 = res[i + j];
    K___uint64_t_uint64_t uu____116 = Multiplication_add64(uu____121, s1);
    K___uint64_t_uint64_t scrut0 = uu____116;
    uint64_t carry2 = scrut0.fst;
    uint64_t s2 = scrut0.snd;
    K___uint64_t_uint64_t uu____124 = Multiplication_add64(s2, carry);
    K___uint64_t_uint64_t scrut1 = uu____124;
    uint64_t carry3 = scrut1.fst;
    uint64_t s3 = scrut1.snd;
    uint64_t carry4 = carry1 + carry2 + carry3;
    res[i + j] = s3;
    Multiplication_mult_inner_loop(aLen, a, b, i, j + (uint32_t )1, carry4, res);
  }
  else
    res[i + aLen] = carry;
}

void
Multiplication_mult_outer_loop(
  uint32_t aLen,
  uint32_t bLen,
  uint64_t *a,
  uint64_t *b,
  uint32_t i,
  uint64_t *res
)
{
  if (i < bLen)
  {
    Multiplication_mult_inner_loop(aLen, a, b, i, (uint32_t )0, (uint64_t )0, res);
    Multiplication_mult_outer_loop(aLen, bLen, a, b, i + (uint32_t )1, res);
  }
}

void Multiplication_mult(uint32_t aLen, uint32_t bLen, uint64_t *a, uint64_t *b, uint64_t *res)
{
  Multiplication_mult_outer_loop(aLen, bLen, a, b, (uint32_t )0, res);
}

void Multiplication_sqr(uint32_t aLen, uint64_t *a, uint64_t *res)
{
  Multiplication_mult(aLen, aLen, a, a, res);
}

