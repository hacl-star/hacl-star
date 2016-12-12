#include "Hacl_EC_Point.h"

uint64_t *Hacl_EC_Point_getx(uint64_t *p)
{
  return p + (uint32_t )0;
}

uint64_t *Hacl_EC_Point_gety(uint64_t *p)
{
  return p + (uint32_t )0;
}

uint64_t *Hacl_EC_Point_getz(uint64_t *p)
{
  return p + (uint32_t )5;
}

uint64_t *Hacl_EC_Point_make(uint64_t *x, uint64_t *y, uint64_t *z)
{
  return x;
}

bool Hacl_EC_Point_valid(FStar_HyperStack_mem h, uint64_t *p)
{
  return (bool )(uint8_t )0;
}

void Hacl_EC_Point_swap_conditional_(uint64_t *a, uint64_t *b, uint64_t swap, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    uint64_t ai0 = a[i];
    uint64_t bi0 = b[i];
    uint64_t x = swap & (ai0 ^ bi0);
    uint64_t ai = ai0 ^ x;
    uint64_t bi = bi0 ^ x;
    a[i] = ai;
    b[i] = bi;
    Hacl_EC_Point_swap_conditional_(a, b, swap, i);
    return;
  }
}

void Hacl_EC_Point_swap_conditional(uint64_t *a, uint64_t *b, uint64_t iswap)
{
  uint64_t swap = (uint64_t )0 - iswap;
  Hacl_EC_Point_swap_conditional_(Hacl_EC_Point_getx(a),
    Hacl_EC_Point_getx(b),
    swap,
    (uint32_t )5);
  Hacl_EC_Point_swap_conditional_(Hacl_EC_Point_getz(a),
    Hacl_EC_Point_getz(b),
    swap,
    (uint32_t )5);
  return;
}

void Hacl_EC_Point_copy(uint64_t *output, uint64_t *input)
{
  memcpy(Hacl_EC_Point_getx(output),
    Hacl_EC_Point_getx(input),
    (uint32_t )5 * sizeof Hacl_EC_Point_getx(input)[0]);
  memcpy(Hacl_EC_Point_getz(output),
    Hacl_EC_Point_getz(input),
    (uint32_t )5 * sizeof Hacl_EC_Point_getz(input)[0]);
}

