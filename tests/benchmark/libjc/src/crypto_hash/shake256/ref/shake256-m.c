#include "crypto_hash.h"
#include "impl.h"
#include "api.h"
#include <string.h>
#include <stdint.h>


extern void keccak_1600(
         uint8_t *out,
        uint64_t outlen,
   const uint8_t *in,
          size_t inlen,
        uint64_t *c
);


int shake256_ref(unsigned char *out,const unsigned char *in,unsigned long long inlen)
{
  uint64_t c[] = {0x1F, (1088/8)};
  keccak_1600(out, 136, in, inlen, c);
  return 0;
}
