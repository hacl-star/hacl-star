#include "crypto_stream.h"
#include "Chacha20_Vec128.h"

int crypto_stream_xor(
        unsigned char *out,
        const unsigned char *in,
        unsigned long long inlen,
        const unsigned char *n,
        const unsigned char *k
		      ){

  Chacha20_Vec128_chacha20(out, in, inlen, k, n, 0);
  return 0;
}


int crypto_stream(
                                  unsigned char *out,
                                  unsigned long long outlen,
                                  const unsigned char *n,
                                  const unsigned char *k
                                  )
{
    memset(out,0,outlen);
    return crypto_stream_xor(out,out,outlen,n,k);
}
