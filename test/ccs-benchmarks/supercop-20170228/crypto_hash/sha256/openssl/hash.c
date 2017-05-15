#include <stddef.h>
#include <openssl/sha.h>
#include "crypto_hash.h"

int crypto_hash(unsigned char *out,const unsigned char *in,unsigned long long inlen)
{
  SHA256(in,inlen,out);
  return 0;
}
