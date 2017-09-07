#include "Hacl_Hash_Lib_LoadStore.h"

void
Hacl_Hash_Lib_LoadStore_uint32s_from_be_bytes(uint32_t *output, uint8_t *input, uint32_t len)
{
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint8_t *x0 = input + (uint32_t )4 * i;
    uint32_t inputi = load32_be(x0);
    output[i] = inputi;
  }
}

void
Hacl_Hash_Lib_LoadStore_uint32s_to_be_bytes(uint8_t *output, uint32_t *input, uint32_t len)
{
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint32_t hd1 = input[i];
    uint8_t *x0 = output + (uint32_t )4 * i;
    store32_be(x0, hd1);
  }
}

void
Hacl_Hash_Lib_LoadStore_uint64s_from_be_bytes(uint64_t *output, uint8_t *input, uint32_t len)
{
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint8_t *x0 = input + (uint32_t )8 * i;
    uint64_t inputi = load64_be(x0);
    output[i] = inputi;
  }
}

void
Hacl_Hash_Lib_LoadStore_uint64s_to_be_bytes(uint8_t *output, uint64_t *input, uint32_t len)
{
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint64_t hd1 = input[i];
    uint8_t *x0 = output + (uint32_t )8 * i;
    store64_be(x0, hd1);
  }
}

