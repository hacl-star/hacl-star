#include "crypto_scalarmult.h"

static const unsigned char base[48] = {
  6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0x68,0x30,0x1e,0x6b,0x4d,0xaf,0xc7,0x56,0x9d,0x1f,0xa7,0xf8,0x71,0x39,0x37,0x6b,
  1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
} ;

int crypto_scalarmult_base(unsigned char *q,const unsigned char *n)
{
  return crypto_scalarmult(q,n,base);
}
