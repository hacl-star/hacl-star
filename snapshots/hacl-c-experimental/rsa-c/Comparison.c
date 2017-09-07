#include "Comparison.h"

bool Comparison_isMore_loop(uint64_t *a, uint64_t *b, uint32_t count1)
{
  bool res;
  if (count1 > (uint32_t )0)
  {
    uint32_t count2 = count1 - (uint32_t )1;
    uint64_t t1 = a[count2];
    uint64_t t2 = b[count2];
    bool ite0;
    if (!(t1 == t2))
    {
      bool ite;
      if (t1 > t2)
        ite = true;
      else
        ite = false;
      ite0 = ite;
    }
    else
      ite0 = Comparison_isMore_loop(a, b, count2);
    res = ite0;
  }
  else
    res = false;
  return res;
}

bool Comparison_isMore(uint32_t aLen, uint32_t bLen, uint64_t *a, uint64_t *b)
{
  bool res;
  if (aLen > bLen)
    res = true;
  else
  {
    bool ite;
    if (aLen < bLen)
      ite = false;
    else
      ite = Comparison_isMore_loop(a, b, aLen);
    res = ite;
  }
  return res;
}

