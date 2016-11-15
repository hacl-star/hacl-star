#include "Hacl_Box.h"

uint32_t Hacl_Box_crypto_box_beforenm(uint8_t *k, uint8_t *pk, uint8_t *sk)
{
  uint8_t tmp[48] = { 0 };
  uint8_t *hsalsa_k = tmp + (uint32_t )0;
  uint8_t *hsalsa_n = tmp + (uint32_t )32;
  Hacl_EC_Curve25519_exp(hsalsa_k, pk, sk);
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(k, hsalsa_n, hsalsa_k);
  return (uint32_t )0;
}

uint32_t
Hacl_Box_crypto_box_detached_afternm(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  return Hacl_SecretBox_crypto_secretbox_detached(c, mac, m, mlen, n, k);
}

void
Hacl_Box_lemma_modifies_3_2(
  uint8_t *c,
  uint8_t *mac,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2
)
{
  return;
}

uint32_t
Hacl_Box_crypto_box_detached(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
)
{
  uint8_t key[80] = { 0 };
  uint8_t *k = key + (uint32_t )0;
  uint8_t *subkey = key + (uint32_t )32;
  uint8_t *hsalsa_n = key + (uint32_t )64;
  Hacl_EC_Curve25519_exp(k, pk, sk);
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(subkey, hsalsa_n, k);
  uint32_t z = Hacl_SecretBox_crypto_secretbox_detached(c, mac, m, mlen, n, subkey);
  return z;
}

uint32_t
Hacl_Box_crypto_box_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
)
{
  uint8_t key[80] = { 0 };
  uint8_t *k = key + (uint32_t )0;
  uint8_t *subkey = key + (uint32_t )32;
  uint8_t *hsalsa_n = key + (uint32_t )64;
  Hacl_EC_Curve25519_exp(k, pk, sk);
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(subkey, hsalsa_n, k);
  uint32_t z = Hacl_SecretBox_crypto_secretbox_open_detached(m, c, mac, mlen, n, subkey);
  return z;
}

uint32_t
Hacl_Box_crypto_box_easy_afternm(uint8_t *c, uint8_t *m, uint64_t mlen, uint8_t *n, uint8_t *k)
{
  return
    Hacl_Box_crypto_box_detached_afternm(c + (uint32_t )16,
      c + (uint32_t )0,
      m + (uint32_t )0,
      mlen,
      n,
      k);
}

uint32_t
Hacl_Box_crypto_box_easy(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
)
{
  return
    Hacl_Box_crypto_box_detached(c + (uint32_t )16,
      c + (uint32_t )0,
      m + (uint32_t )0,
      mlen,
      n,
      pk,
      sk);
}

uint32_t
Hacl_Box_crypto_box_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
)
{
  uint8_t *mac = c + (uint32_t )0;
  return
    Hacl_Box_crypto_box_open_detached(m,
      c + (uint32_t )16,
      mac,
      mlen - (uint64_t )16,
      n,
      pk,
      sk);
}

uint32_t
Hacl_Box_crypto_box_open_detached_afternm(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  return Hacl_SecretBox_crypto_secretbox_open_detached(m, c, mac, mlen, n, k);
}

uint32_t
Hacl_Box_crypto_box_open_easy_afternm(
  uint8_t *m,
  uint8_t *c,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  uint8_t *mac = c + (uint32_t )0;
  uint8_t *c0 = c + (uint32_t )16;
  return Hacl_Box_crypto_box_open_detached_afternm(m, c0, mac, mlen - (uint64_t )16, n, k);
}

