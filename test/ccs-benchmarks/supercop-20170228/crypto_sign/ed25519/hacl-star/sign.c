#include "crypto_sign.h"
#include "Ed25519.h"

int crypto_sign(
  unsigned char *sm,unsigned long long *smlen,
  const unsigned char *m,unsigned long long mlen,
  const unsigned char *sk
)
{

  Ed25519_sign(sm,sk,m,mlen);
}

int crypto_sign_open(
  unsigned char *m,unsigned long long *mlen,
  const unsigned char *sm,unsigned long long smlen,
  const unsigned char *pk
)
{

  Ed25519_verify(pk,m,mlen,sm);
}
