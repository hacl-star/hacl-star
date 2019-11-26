#include "crypto_stream.h"
#include "impl.h"
#include <string.h>
#include <stdint.h>

extern void chacha20_impl(
  unsigned char *out,
  const unsigned char *in,
  unsigned long long inlen,
  const unsigned char *k,
  const unsigned char *n,
  unsigned int counter
);

int crypto_stream(
  unsigned char *out,
  unsigned long long outlen,
  const unsigned char *n,
  const unsigned char *k
)
{
  unsigned char nonce[12];
  memset(out, 0, outlen);
  memset(nonce, 0, 4);
  memcpy(nonce+4, n, 8);
	chacha20_impl(out, out, outlen, k, nonce, 0);
	return 0;
}

int crypto_stream_xor(
  unsigned char *out,
  const unsigned char *in,
  unsigned long long inlen,
  const unsigned char *n,
  const unsigned char *k
)
{
  unsigned char nonce[12];
  memset(nonce, 0, 4);
  memcpy(nonce+4, n, 8);
	chacha20_impl(out, in, inlen, k, nonce, 0);
	return 0;
}
