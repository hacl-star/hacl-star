#include "Exponentiation.h"

uint32_t Exponentiation_bn_bits2 = (uint32_t )64;

bool Exponentiation_bn_bit_is_set(uint64_t *input, uint32_t ind)
{
  uint32_t i = ind / Exponentiation_bn_bits2;
  uint32_t j = ind % Exponentiation_bn_bits2;
  uint64_t tmp = input[i];
  bool res = (tmp >> j & (uint64_t )1) == (uint64_t )1;
  return res;
}

void
Exponentiation_mod_exp_loop(
  uint32_t modBits,
  uint32_t aLen,
  uint32_t bBits,
  uint32_t resLen,
  uint64_t *n1,
  uint64_t *tmpV,
  uint64_t *b,
  uint64_t *res,
  uint32_t count1
)
{
  uint32_t tmpLen = (uint32_t )2 * aLen;
  KRML_CHECK_SIZE((uint64_t )0, tmpLen);
  uint64_t tmp[tmpLen];
  memset(tmp, 0, tmpLen * sizeof tmp[0]);
  uint32_t tmpBits = tmpLen * (uint32_t )64;
  uint32_t tmpLen2 = aLen + resLen;
  KRML_CHECK_SIZE((uint64_t )0, tmpLen2);
  uint64_t tmp2[tmpLen2];
  memset(tmp2, 0, tmpLen2 * sizeof tmp2[0]);
  uint32_t tmpBits2 = tmpLen2 * (uint32_t )64;
  if (count1 < bBits)
  {
    Multiplication_sqr(aLen, tmpV, tmp);
    Division_remainder(tmpBits, modBits, aLen, tmp, n1, tmpV);
    bool uu____136 = Exponentiation_bn_bit_is_set(b, count1);
    if (uu____136)
    {
      Multiplication_mult(resLen, aLen, res, tmpV, tmp2);
      Division_remainder(tmpBits2, modBits, resLen, tmp2, n1, res);
    }
    Exponentiation_mod_exp_loop(modBits,
      aLen,
      bBits,
      resLen,
      n1,
      tmpV,
      b,
      res,
      count1 + (uint32_t )1);
  }
}

void
Exponentiation_mod_exp(
  uint32_t modBits,
  uint32_t aLen,
  uint32_t bBits,
  uint32_t resLen,
  uint64_t *n1,
  uint64_t *a,
  uint64_t *b,
  uint64_t *res
)
{
  KRML_CHECK_SIZE((uint64_t )0, aLen);
  uint64_t tmpV[aLen];
  memset(tmpV, 0, aLen * sizeof tmpV[0]);
  memcpy(tmpV, a, aLen * sizeof a[0]);
  bool uu____219 = Exponentiation_bn_bit_is_set(b, (uint32_t )0);
  if (uu____219)
    memcpy(res, a, aLen * sizeof a[0]);
  else
    res[0] = (uint64_t )1;
  Exponentiation_mod_exp_loop(modBits, aLen, bBits, resLen, n1, b, res, tmpV, (uint32_t )1);
}

