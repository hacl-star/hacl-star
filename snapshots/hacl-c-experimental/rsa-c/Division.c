#include "Division.h"

uint32_t Division_bn_bits2 = (uint32_t )64;

void
Division_remainder_loop(
  uint32_t rLen,
  uint32_t modLen,
  uint32_t resLen,
  uint64_t *r_i,
  uint64_t *mod_78,
  uint32_t count1,
  uint64_t *res
)
{
  uint64_t uu____90 = mod_78[modLen - (uint32_t )1];
  bool uu____89 = uu____90 == (uint64_t )1;
  uint32_t isSet;
  if (uu____89)
    isSet = (uint32_t )1;
  else
    isSet = (uint32_t )0;
  uint32_t mod1Len = modLen - isSet;
  KRML_CHECK_SIZE((uint64_t )0, mod1Len);
  uint64_t mod1[mod1Len];
  memset(mod1, 0, mod1Len * sizeof mod1[0]);
  KRML_CHECK_SIZE((uint64_t )0, rLen);
  uint64_t tmp[rLen];
  memset(tmp, 0, rLen * sizeof tmp[0]);
  if (count1 > (uint32_t )0)
  {
    Shift_rshift1(modLen, mod_78, mod1);
    bool uu____104 = Comparison_isMore(modLen, rLen, mod_78, r_i);
    bool uu____103 = !uu____104;
    if (uu____103)
    {
      Addition_sub(rLen, modLen, r_i, mod_78, tmp);
      memcpy(r_i, tmp, rLen * sizeof tmp[0]);
      Division_remainder_loop(rLen, mod1Len, resLen, r_i, mod1, count1 - (uint32_t )1, res);
    }
    else
      Division_remainder_loop(rLen, mod1Len, resLen, r_i, mod1, count1 - (uint32_t )1, res);
  }
  else
  {
    uint32_t len;
    if (resLen > rLen)
      len = rLen;
    else
      len = resLen;
    memcpy(res, r_i, len * sizeof r_i[0]);
  }
}

void
Division_remainder(
  uint32_t aBits,
  uint32_t modBits,
  uint32_t resLen,
  uint64_t *a,
  uint64_t *mod_183,
  uint64_t *res
)
{
  uint32_t aLen = Convert_bits_to_bn(aBits);
  uint32_t modLen = Convert_bits_to_bn(modBits);
  uint32_t k = aBits - modBits;
  uint32_t modk = k / Division_bn_bits2;
  uint32_t mod1Len = modLen + modk;
  KRML_CHECK_SIZE((uint64_t )0, mod1Len);
  uint64_t mod1[mod1Len];
  memset(mod1, 0, mod1Len * sizeof mod1[0]);
  Shift_lshift(modLen, mod_183, k, mod1);
  Division_remainder_loop(aLen, mod1Len, resLen, a, mod1, k, res);
}

