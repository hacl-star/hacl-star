#include "Random.h"

uint32_t random_uint32()
{
  uint32_t rr32[1] = { 0 };
  rdrand32_step(rr32);
  uint32_t r = rr32[(uint32_t )0];
  return r;
}

uint64_t random_uint64()
{
  uint64_t rr64[1] = { 0 };
  rdrand64_step(rr64);
  uint64_t r = rr64[(uint32_t )0];
  return r;
}

void random_bytes(uint8_t *rand, uint32_t n)
{
  rdrand_get_bytes(n, rand);
  return;
}

uint32_t randseed_uint32()
{
  uint32_t rs32[1] = { 0 };
  rdseed32_step(rs32);
  uint32_t r = rs32[(uint32_t )0];
  return r;
}

uint64_t randseed_uint64()
{
  uint64_t rs64[1] = { 0 };
  rdseed64_step(rs64);
  uint64_t r = rs64[(uint32_t )0];
  return r;
}

