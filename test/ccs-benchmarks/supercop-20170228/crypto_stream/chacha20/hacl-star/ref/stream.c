#include "crypto_stream.h"
#include "Chacha20.h"

int crypto_stream_xor(
        unsigned char *out,
        const unsigned char *in,
        unsigned long long inlen,
        const unsigned char *n,
        const unsigned char *k
		      ){

  Chacha20_chacha20(out, in, inlen, k, n, 0);
  return 0;
}


int crypto_stream(
                                  unsigned char *out,
                                  unsigned long long outlen,
                                  const unsigned char *n,
                                  const unsigned char *k
                                  )
{
  uint32_t ctr = 0;
  uint8_t block[64];
  while (outlen >= 64) {
    Chacha20_chacha20_key_block(out,k,n,ctr);
    out += 64;
    ctr ++;
    outlen -= 64;
  }
  if (outlen > 0) {
    Chacha20_chacha20_key_block(block,k,n,ctr);
    memcpy(out,block,outlen);
  }
  return 0;
}
