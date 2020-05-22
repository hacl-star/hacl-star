#include <stdint.h>
#include "Lib_Memzero0.h"

void clear_words(void* mem, unsigned int nwords)
{ // Clear 32-bit words from memory. "nwords" indicates the number of words to be zeroed.
  Lib_Memzero0_memzero(mem, 4*len);
}

void Lib_Memzero_clear_words_u16(unsigned int nwords, uint16_t *mem)
{
  Lib_Memzero0_memzero((void*)mem, 2*nwords);
}

void Lib_Memzero_clear_words_u8(unsigned int nwords, uint8_t *mem)
{
  Lib_Memzero0_memzero((void*)mem, nwords);
}
