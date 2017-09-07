#include "Convert.h"

uint32_t Convert_bn_bytes = (uint32_t )8;

uint32_t Convert_get_size_nat(uint32_t lenText)
{
  return (lenText - (uint32_t )1) / Convert_bn_bytes + (uint32_t )1;
}

uint32_t Convert_bits_to_bn(uint32_t bits)
{
  return
    ((bits - (uint32_t )1) / (uint32_t )8 + (uint32_t )1 - (uint32_t )1)
    / (uint32_t )8
    + (uint32_t )1;
}

uint32_t Convert_bits_to_text(uint32_t bits)
{
  return (bits - (uint32_t )1) / (uint32_t )8 + (uint32_t )1;
}

void
Convert_text_to_nat_loop(
  uint8_t *input,
  uint32_t len,
  uint64_t *res,
  uint32_t num_words,
  uint32_t m,
  uint64_t word,
  uint32_t i
)
{
  if (len > (uint32_t )0)
  {
    uint32_t len1 = len - (uint32_t )1;
    uint8_t tmp = input[i];
    uint64_t word1 = word << (uint32_t )8 | (uint64_t )tmp;
    uint32_t i1 = i + (uint32_t )1;
    if (m == (uint32_t )0)
    {
      uint32_t num_words1 = num_words - (uint32_t )1;
      res[num_words1] = word1;
      uint64_t word2 = (uint64_t )0;
      uint32_t m1 = Convert_bn_bytes - (uint32_t )1;
      Convert_text_to_nat_loop(input, len1, res, num_words1, m1, word2, i1);
    }
    else
      Convert_text_to_nat_loop(input, len1, res, num_words, m - (uint32_t )1, word1, i1);
  }
}

void Convert_text_to_nat(uint8_t *input, uint32_t len, uint64_t *res)
{
  uint32_t num_words = Convert_get_size_nat(len);
  uint32_t m = (len - (uint32_t )1) % Convert_bn_bytes;
  Convert_text_to_nat_loop(input, len, res, num_words, m, (uint64_t )0, (uint32_t )0);
}

void Convert_nat_to_text_loop(uint64_t *input, uint8_t *res, uint32_t i, uint32_t j)
{
  if (i > (uint32_t )0)
  {
    uint32_t i1 = i - (uint32_t )1;
    uint32_t ind = i1 / Convert_bn_bytes;
    uint64_t l = input[ind];
    uint32_t tmp = i1 % Convert_bn_bytes;
    res[j] = (uint8_t )(l >> (uint32_t )8 * tmp) & (uint8_t )0xff;
    Convert_nat_to_text_loop(input, res, i1, j + (uint32_t )1);
  }
}

void Convert_nat_to_text(uint64_t *input, uint32_t len, uint8_t *res)
{
  Convert_nat_to_text_loop(input, res, len, (uint32_t )0);
}

