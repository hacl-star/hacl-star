#include <stdint.h>
#include "Lib_Memzero0.h"

void Lib_Memzero_clear_words_u16(unsigned int nwords, uint16_t *mem)
{
  Lib_Memzero0_memzero((void*)mem, 2*nwords);
}

void Lib_Memzero_clear_words_u8(unsigned int nwords, uint8_t *mem)
{
  Lib_Memzero0_memzero((void*)mem, nwords);
}
