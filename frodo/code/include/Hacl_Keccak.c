#include "fips202.h"

void Hacl_Keccak_cshake128_frodo(uint32_t inlen, uint8_t *in, uint16_t cstm, uint32_t outlen, uint8_t *output)
{
 cshake128_simple(output, outlen, cstm, in, inlen);
}

void Hacl_Keccak_cshake256_frodo(uint32_t inlen, uint8_t *in, uint16_t cstm, uint32_t outlen, uint8_t *output)
{
 cshake256_simple(output, outlen, cstm, in, inlen);
}
