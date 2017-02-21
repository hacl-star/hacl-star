#include "NaCl.h"

uint32_t
Hacl_SecretBox_crypto_secretbox_detached(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  /* assume that plaintext starts at m+32 */
  /* assume that ciphertext starts at c+32 */
  uint8_t subkey[32];
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(subkey, n + (uint32_t )0, k);
  Salsa20_crypto_stream_salsa20_xor(c,
				    m,
				    mlen,
				    n+16,
				    subkey);
  Poly1305_64_crypto_onetimeauth(mac, c+32, mlen, c);
  memset(c,0,32);
  return (uint32_t )0;
}

uint32_t
Hacl_SecretBox_crypto_secretbox_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t clen,
  uint8_t *n,
  uint8_t *k
)
{
  uint8_t hsalsa_state[112] = { 0 };
  uint8_t *subkey = hsalsa_state + (uint32_t )0;
  uint8_t *block0 = hsalsa_state + (uint32_t )32;
  uint8_t *tmp_mac = hsalsa_state + (uint32_t )96;
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(subkey, n, k);
  Salsa20_crypto_stream_salsa20(block0, (uint64_t )32, n + (uint32_t )16, subkey);
  Poly1305_64_crypto_onetimeauth(tmp_mac, c+32, clen, block0 + (uint32_t )0);
  uint8_t verify = Hacl_Policies_cmp_bytes(mac, tmp_mac, (uint32_t )16);
  if (verify == (uint8_t )0)
  {
      memset(c,0,32);
      Salsa20_crypto_stream_salsa20_xor(m,
        c,
	clen, 
        n + (uint32_t )16,
        subkey); 
      memset(m,0,32);
  }
  return verify;
}

uint32_t
Hacl_SecretBox_crypto_secretbox_easy(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  uint8_t mac[16];
  int res = Hacl_SecretBox_crypto_secretbox_detached(c, mac, m, mlen, n, k);
  memcpy(c+16,mac,16);
}

uint32_t
Hacl_SecretBox_crypto_secretbox_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint64_t clen,
  uint8_t *n,
  uint8_t *k
)
{
  return Hacl_SecretBox_crypto_secretbox_open_detached(m, c, c+16, clen - (uint64_t )16, n, k);
}


uint32_t Hacl_Box_crypto_box_beforenm(uint8_t *k, uint8_t *pk, uint8_t *sk)
{
  uint8_t tmp[48] = { 0 };
  uint8_t *hsalsa_k = tmp + (uint32_t )0;
  uint8_t *hsalsa_n = tmp + (uint32_t )32;
  Curve25519_crypto_scalarmult(hsalsa_k, sk, pk);
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
  Curve25519_crypto_scalarmult(k, sk, pk);
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
  Curve25519_crypto_scalarmult(k, sk, pk);
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
  uint8_t key[80] = { 0 };
  uint8_t *k = key + (uint32_t )0;
  uint8_t *subkey = key + (uint32_t )32;
  uint8_t *hsalsa_n = key + (uint32_t )64;
  Curve25519_crypto_scalarmult(k, sk, pk);
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(subkey, hsalsa_n, k);


  //  uint8_t mac[16];
  // uint32_t z = Hacl_SecretBox_crypto_secretbox_detached(c, mac, m, mlen, n, subkey);
  // memcpy(c+16,mac,16);

  int res = 
    Hacl_SecretBox_crypto_secretbox_easy(c,
				   m ,
				   mlen,
				   n,
				   subkey);
  
}

uint32_t
Hacl_Box_crypto_box_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint64_t clen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
)
{
  uint8_t key[80] = { 0 };
  uint8_t *k = key + (uint32_t )0;
  uint8_t *subkey = key + (uint32_t )32;
  uint8_t *hsalsa_n = key + (uint32_t )64;
  Curve25519_crypto_scalarmult(k, sk, pk);
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(subkey, hsalsa_n, k);
  uint32_t z = Hacl_SecretBox_crypto_secretbox_open_easy(m, c, clen, n, subkey);
  return z;
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

