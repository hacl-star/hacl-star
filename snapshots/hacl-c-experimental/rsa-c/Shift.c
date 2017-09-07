#include "Shift.h"

uint32_t Shift_bn_bits2 = (uint32_t )64;

uint64_t Shift_bn_tbit = (uint64_t )0x8000000000000000;

uint64_t Shift_bn_mask2 = (uint64_t )0xffffffffffffffff;

void Shift_lshift_loop(uint64_t *a, uint32_t count1, uint32_t nw, uint32_t lb, uint64_t *res)
{
  if (count1 > (uint32_t )0)
  {
    uint32_t count2 = count1 - (uint32_t )1;
    uint64_t l = a[count2];
    uint32_t ind = nw + count2 + (uint32_t )1;
    uint32_t rb = Shift_bn_bits2 - lb;
    uint64_t tmp = res[ind];
    res[ind] = tmp | l >> rb & Shift_bn_mask2;
    res[ind - (uint32_t )1] = l << lb & Shift_bn_mask2;
    Shift_lshift_loop(a, count2, nw, lb, res);
  }
}

void Shift_lshift(uint32_t aLen, uint64_t *a, uint32_t nCount, uint64_t *res)
{
  uint32_t nw = nCount / Shift_bn_bits2;
  (void )(aLen + nw);
  uint32_t lb = nCount % Shift_bn_bits2;
  if (lb == (uint32_t )0)
    memcpy(res + nw, a, aLen * sizeof a[0]);
  else
    Shift_lshift_loop(a, aLen, nw, lb, res);
}

void Shift_rshift1_loop(uint64_t *a, uint64_t carry, uint32_t ind, uint64_t *res)
{
  if (ind > (uint32_t )0)
  {
    uint32_t ind1 = ind - (uint32_t )1;
    uint64_t tmp = a[ind1];
    res[ind1] = tmp >> (uint32_t )1 & Shift_bn_mask2 | carry;
    uint64_t carry1;
    if ((tmp & (uint64_t )1) == (uint64_t )1)
      carry1 = Shift_bn_tbit;
    else
      carry1 = (uint64_t )0;
    Shift_rshift1_loop(a, carry1, ind1, res);
  }
}

void Shift_rshift1(uint32_t aLen, uint64_t *a, uint64_t *res)
{
  uint32_t i = aLen - (uint32_t )1;
  uint64_t tmp = a[i];
  uint64_t carry;
  if ((tmp & (uint64_t )1) == (uint64_t )1)
    carry = Shift_bn_tbit;
  else
    carry = (uint64_t )0;
  uint64_t tmp1 = tmp >> (uint32_t )1;
  if (tmp1 > (uint64_t )0)
    res[i] = tmp1;
  Shift_rshift1_loop(a, carry, i, res);
}

