#include "Chacha20Poly1305.h"

Prims_int Chacha20Poly1305_noncelen;

Prims_int Chacha20Poly1305_keylen;

Prims_int Chacha20Poly1305_maclen;

static void
Chacha20Poly1305_aead_encrypt_poly(
  uint8_t *c,
  uint32_t mlen,
  uint8_t *mac,
  uint8_t *aad,
  uint32_t aadlen,
  uint8_t *tmp
)
{
  uint8_t *b = tmp;
  uint8_t *lb = tmp + (uint32_t )64;
  uint8_t *mk = b;
  uint8_t *key_s = mk + (uint32_t )16;
  KRML_CHECK_SIZE((uint64_t )0, (uint32_t )6);
  uint64_t tmp0[6] = { 0 };
  Hacl_Impl_Poly1305_64_poly1305_state st = Poly1305_64_mk_state(tmp0, tmp0 + (uint32_t )3);
  Poly1305_64_poly1305_blocks_init(st, aad, aadlen, mk);
  Poly1305_64_poly1305_blocks_continue((void *)(uint8_t )0, st, c, mlen);
  Poly1305_64_poly1305_blocks_finish((void *)(uint8_t )0, st, lb, mac, key_s);
}

void Chacha20Poly1305_encode_length(uint8_t *lb, uint32_t aad_len, uint32_t mlen)
{
  uint8_t *x0 = lb;
  store64_le(x0, (uint64_t )aad_len);
  uint8_t *x00 = lb + (uint32_t )8;
  store64_le(x00, (uint64_t )mlen);
  return;
}

uint32_t
Chacha20Poly1305_aead_encrypt_(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *aad,
  uint32_t aadlen,
  uint8_t *k,
  uint8_t *n
)
{
  KRML_CHECK_SIZE((uint8_t )0, (uint32_t )80);
  uint8_t tmp[80] = { 0 };
  uint8_t *b = tmp;
  uint8_t *lb = tmp + (uint32_t )64;
  Chacha20Poly1305_encode_length(lb, aadlen, mlen);
  Chacha20_chacha20(c, m, mlen, k, n, (uint32_t )1);
  Chacha20_chacha20_key_block(b, k, n, (uint32_t )0);
  Chacha20Poly1305_aead_encrypt_poly(c, mlen, mac, aad, aadlen, tmp);
  return (uint32_t )0;
}

uint32_t
Chacha20Poly1305_aead_encrypt(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *aad,
  uint32_t aadlen,
  uint8_t *k,
  uint8_t *n
)
{
  uint32_t z = Chacha20Poly1305_aead_encrypt_(c, mac, m, mlen, aad, aadlen, k, n);
  return z;
}

uint32_t
Chacha20Poly1305_aead_decrypt(
  uint8_t *m,
  uint8_t *c,
  uint32_t mlen,
  uint8_t *mac,
  uint8_t *aad,
  uint32_t aadlen,
  uint8_t *k,
  uint8_t *n
)
{
  KRML_CHECK_SIZE((uint8_t )0, (uint32_t )96);
  uint8_t tmp[96] = { 0 };
  uint8_t *b = tmp;
  uint8_t *lb = tmp + (uint32_t )64;
  Chacha20Poly1305_encode_length(lb, aadlen, mlen);
  uint8_t *rmac = tmp + (uint32_t )80;
  Chacha20_chacha20_key_block(b, k, n, (uint32_t )0);
  uint8_t *mk = b;
  uint8_t *key_s = mk + (uint32_t )16;
  Chacha20Poly1305_aead_encrypt_poly(c, mlen, rmac, aad, aadlen, tmp);
  uint8_t verify = Hacl_Policies_cmp_bytes(mac, rmac, (uint32_t )16);
  uint32_t res;
  if (verify == (uint8_t )0)
  {
    Chacha20_chacha20(m, c, mlen, k, n, (uint32_t )1);
    res = (uint32_t )0;
  }
  else
    res = (uint32_t )1;
  return res;
}

