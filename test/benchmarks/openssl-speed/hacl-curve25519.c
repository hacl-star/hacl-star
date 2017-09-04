
void X25519(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint)
{
  Hacl_EC_crypto_scalarmult(mypublic, secret, basepoint);
  return;
}


void X25519_public_from_private(uint8_t *mypublic, uint8_t *secret)
{
  uint8_t basepoint[32] = {9};
  Hacl_EC_crypto_scalarmult(mypublic, secret, basepoint);
  return;
}

