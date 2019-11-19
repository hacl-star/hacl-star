#include "crypto_verify_16.h"
#include "crypto_onetimeauth.h"
#include "impl.h"

extern void poly1305_impl(
  unsigned char *out,
  const unsigned char *in,
  unsigned long long inlen,
  const unsigned char *k
);

int crypto_onetimeauth(
  unsigned char *out,
  const unsigned char *in,
  unsigned long long inlen,
  const unsigned char *k
)
{
  poly1305_impl(out, in, inlen, k);
  return 0;
}

int crypto_onetimeauth_verify(
  const unsigned char *h,
  const unsigned char *in,
  unsigned long long inlen,
  const unsigned char *k
)
{
  unsigned char correct[16];
  crypto_onetimeauth(correct,in,inlen,k);
  return crypto_verify_16(h,correct);
}
