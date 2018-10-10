#include "fips202.h"
#include "fips202x4.h"

void Hacl_Keccak_cshake128_frodo(uint32_t inlen, uint8_t *in, uint16_t cstm, uint32_t outlen, uint8_t *output)
{
 cshake128_simple(output, outlen, cstm, in, inlen);
}

void Hacl_Keccak_cshake128_frodo_4x(uint32_t inlen, uint8_t *in, uint16_t cstm0, uint16_t cstm1, uint16_t cstm2, uint16_t cstm3, 
		uint32_t outlen, uint8_t *output0, uint8_t *output1, uint8_t *output2, uint8_t *output3)
{
 cshake128_simple4x(output0, output1, output2, output3, outlen, cstm0, cstm1, cstm2, cstm3, in, inlen);
}

void Hacl_Keccak_cshake256_frodo(uint32_t inlen, uint8_t *in, uint16_t cstm, uint32_t outlen, uint8_t *output)
{
 cshake256_simple(output, outlen, cstm, in, inlen);
}

void Hacl_Keccak_cshake256_frodo_4x(uint32_t inlen, uint8_t *in, uint16_t cstm0, uint16_t cstm1, uint16_t cstm2, uint16_t cstm3, 
		uint32_t outlen, uint8_t *output0, uint8_t *output1, uint8_t *output2, uint8_t *output3)
{
 cshake256_simple4x(output0, output1, output2, output3, outlen, cstm0, cstm1, cstm2, cstm3, in, inlen);
}
