#include "crypto_scalarmult.h"
#include "Curve25519.h"

int crypto_scalarmult(uint8_t *mypublic, const uint8_t *secret, const uint8_t *basepoint)
{
  Curve25519_crypto_scalarmult(mypublic, secret, basepoint);
  return 0;
}

