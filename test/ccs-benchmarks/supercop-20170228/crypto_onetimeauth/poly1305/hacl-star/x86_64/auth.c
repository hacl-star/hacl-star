#include "crypto_verify_16.h"
#include "crypto_onetimeauth.h"
#include "Poly1305_64.h"

int crypto_onetimeauth(unsigned char *output, const unsigned char *input, unsigned long long len, const unsigned char *k)
{
  Poly1305_64_crypto_onetimeauth(output, input, len, k);
  return 0;
}

int crypto_onetimeauth_verify(const unsigned char *h,const unsigned char *in,unsigned long long inlen,const unsigned char *k)
{
  unsigned char correct[16];
  crypto_onetimeauth(correct,in,inlen,k);
  return crypto_verify_16(h,correct);
}
