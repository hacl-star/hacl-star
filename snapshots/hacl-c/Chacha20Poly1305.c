#include "Chacha20Poly1305.h"

Prims_int Chacha20Poly1305_noncelen;

Prims_int Chacha20Poly1305_keylen;

Prims_int Chacha20Poly1305_maclen;

static void
Chacha20Poly1305_aead_encrypt_poly(
  uint8_t *c,
  uint32_t mlen,
  uint8_t *mac,
  uint8_t *aad1,
  uint32_t aadlen,
  uint8_t *tmp
)
{
  uint8_t *b = tmp;
  uint8_t *lb = tmp + (uint32_t )64;
  uint8_t *mk = b;
  uint8_t *key_s = mk + (uint32_t )16;
  uint64_t tmp1[6] = { 0 };
  Hacl_Impl_Poly1305_64_State_poly1305_state
  st = AEAD_Poly1305_64_mk_state(tmp1, tmp1 + (uint32_t )3);
  (void )AEAD_Poly1305_64_poly1305_blocks_init(st, aad1, aadlen, mk);
  (void )AEAD_Poly1305_64_poly1305_blocks_continue(st, c, mlen);
  AEAD_Poly1305_64_poly1305_blocks_finish(st, lb, mac, key_s);
}

void Chacha20Poly1305_encode_length(uint8_t *lb, uint32_t aad_len, uint32_t mlen)
{
  store64_le(lb, (uint64_t )aad_len);
  uint8_t *x0 = lb + (uint32_t )8;
  store64_le(x0, (uint64_t )mlen);
}

uint32_t
Chacha20Poly1305_aead_encrypt_(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *aad1,
  uint32_t aadlen,
  uint8_t *k1,
  uint8_t *n1
)
{
  uint8_t tmp[80] = { 0 };
  uint8_t *b = tmp;
  uint8_t *lb = tmp + (uint32_t )64;
  Chacha20Poly1305_encode_length(lb, aadlen, mlen);
  Chacha20_chacha20(c, m, mlen, k1, n1, (uint32_t )1);
  Chacha20_chacha20_key_block(b, k1, n1, (uint32_t )0);
  Chacha20Poly1305_aead_encrypt_poly(c, mlen, mac, aad1, aadlen, tmp);
  return (uint32_t )0;
}

uint32_t
Chacha20Poly1305_aead_encrypt(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *aad1,
  uint32_t aadlen,
  uint8_t *k1,
  uint8_t *n1
)
{
  uint32_t z = Chacha20Poly1305_aead_encrypt_(c, mac, m, mlen, aad1, aadlen, k1, n1);
  return z;
}

uint32_t
Chacha20Poly1305_aead_decrypt(
  uint8_t *m,
  uint8_t *c,
  uint32_t mlen,
  uint8_t *mac,
  uint8_t *aad1,
  uint32_t aadlen,
  uint8_t *k1,
  uint8_t *n1
)
{
  uint8_t tmp[96] = { 0 };
  uint8_t *b = tmp;
  uint8_t *lb = tmp + (uint32_t )64;
  Chacha20Poly1305_encode_length(lb, aadlen, mlen);
  uint8_t *rmac = tmp + (uint32_t )80;
  Chacha20_chacha20_key_block(b, k1, n1, (uint32_t )0);
  uint8_t *mk = b;
  (void )(mk + (uint32_t )16);
  Chacha20Poly1305_aead_encrypt_poly(c, mlen, rmac, aad1, aadlen, tmp);
  uint8_t result = Hacl_Policies_cmp_bytes(mac, rmac, (uint32_t )16);
  uint8_t verify = result;
  uint32_t res;
  if (verify == (uint8_t )0)
  {
    Chacha20_chacha20(m, c, mlen, k1, n1, (uint32_t )1);
    res = (uint32_t )0;
  }
  else
    res = (uint32_t )1;
  return res;
}

