#include "crypto_sign.h"
#include "randombytes.h"
#include "Ed25519.h"

int crypto_sign_keypair(unsigned char *pk,unsigned char *sk)
{
  randombytes(sk,32);
  Ed25519_secret_to_public(pk,sk);
  memmove(sk + 32,pk,32);
  return 0;
}

int crypto_sign(
  unsigned char *sm,unsigned long long *smlen,
  const unsigned char *m,unsigned long long mlen,
  const unsigned char *sk
)
{
  memmove(sm+64, m, mlen);
  Ed25519_sign(sm, sk, sm+64, mlen);
  *smlen = mlen + 64;
  return 0;
}

int crypto_sign_open(
  unsigned char *m,unsigned long long *mlen,
  const unsigned char *sm,unsigned long long smlen,
  const unsigned char *pk
)
{
  if (Ed25519_verify(pk,sm+64,smlen-64,sm)){
    *mlen = smlen - 64;
    memmove(m,sm+64,smlen-64);
    return 0;
  }
  else {
    *mlen = (unsigned long long) -1;
    return -1;
  }
}
