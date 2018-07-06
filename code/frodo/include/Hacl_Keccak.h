#ifndef __Hacl_Keccak_H
#define __Hacl_Keccak_H

#include "fips202.h"

void Hacl_Keccak_cshake128_frodo(uint32_t x0, uint8_t *x1, uint16_t x2, uint32_t x3, uint8_t *x4);
void Hacl_Keccak_cshake256_frodo(uint32_t x0, uint8_t *x1, uint16_t x2, uint32_t x3, uint8_t *x4);

#endif
