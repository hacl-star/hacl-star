#include "Addition.h"

bool
Addition_sub_loop_min(
  uint32_t bLen,
  uint64_t *a,
  uint64_t *b,
  bool carry,
  uint32_t count1,
  uint64_t *res
)
{
  bool carry10;
  if (count1 < bLen)
  {
    uint64_t t1 = a[count1];
    uint64_t t2 = b[count1];
    bool carry1;
    if (carry)
    {
      res[count1] = t1 - t2 - (uint64_t )1;
      carry1 = t1 <= t2;
    }
    else
    {
      res[count1] = t1 - t2;
      carry1 = t1 < t2;
    }
    carry10 = Addition_sub_loop_min(bLen, a, b, carry1, count1 + (uint32_t )1, res);
  }
  else
    carry10 = carry;
  return carry10;
}

uint32_t
Addition_sub_loop_dif(uint32_t aLen, uint64_t *a, uint32_t ind, uint32_t dif, uint64_t *res)
{
  uint32_t dif10;
  if (dif > (uint32_t )0)
  {
    uint32_t dif1 = dif - (uint32_t )1;
    uint64_t uu____135 = a[ind];
    uint64_t uu____134 = uu____135 - (uint64_t )1;
    res[ind] = uu____134;
    uint32_t ind1 = ind + (uint32_t )1;
    uint64_t uu____138 = a[ind1];
    bool uu____137 = uu____138 == (uint64_t )1;
    uint32_t ite;
    if (uu____137)
      ite = dif1;
    else
      ite = Addition_sub_loop_dif(aLen, a, ind1, dif1, res);
    dif10 = ite;
  }
  else
    dif10 = dif;
  return dif10;
}

void Addition_sub(uint32_t aLen, uint32_t bLen, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint32_t dif = aLen - bLen;
  bool carry = Addition_sub_loop_min(bLen, a, b, false, (uint32_t )0, res);
  uint32_t dif1;
  if (carry)
    dif1 = Addition_sub_loop_dif(aLen, a, bLen, dif, res);
  else
    dif1 = dif;
  if (dif1 > (uint32_t )0)
  {
    uint32_t ind = aLen - dif1;
    memcpy(res + ind, a + ind, dif1 * sizeof a[0]);
  }
}

