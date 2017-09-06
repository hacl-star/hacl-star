/*
20080913
D. J. Bernstein
Public domain.
*/

#include "crypto_hash.h"
#include "SHA2_512.h"

int crypto_hash(unsigned char *out,const unsigned char *in,unsigned long long inlen)
{
  SHA2_512_hash(out,in,inlen);
}
