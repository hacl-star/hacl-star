#include "NaCl.h"

static void Hacl_SecretBox_ZeroPad_set_zero_bytes(uint8_t *b)
{
  uint8_t zero = (uint8_t )0;
  b[0] = zero;
  b[1] = zero;
  b[2] = zero;
  b[3] = zero;
  b[4] = zero;
  b[5] = zero;
  b[6] = zero;
  b[7] = zero;
  b[8] = zero;
  b[9] = zero;
  b[10] = zero;
  b[11] = zero;
  b[12] = zero;
  b[13] = zero;
  b[14] = zero;
  b[15] = zero;
  b[16] = zero;
  b[17] = zero;
  b[18] = zero;
  b[19] = zero;
  b[20] = zero;
  b[21] = zero;
  b[22] = zero;
  b[23] = zero;
  b[24] = zero;
  b[25] = zero;
  b[26] = zero;
  b[27] = zero;
  b[28] = zero;
  b[29] = zero;
  b[30] = zero;
  b[31] = zero;
}

static uint32_t
Hacl_SecretBox_ZeroPad_crypto_secretbox_detached(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  uint8_t subkey[32] = { 0 };
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(subkey, n, k);
  Salsa20_crypto_stream_salsa20_xor(c, m, mlen + (uint64_t )32, n + (uint32_t )16, subkey);
  Poly1305_64_crypto_onetimeauth(mac, c + (uint32_t )32, mlen, c);
  Hacl_SecretBox_ZeroPad_set_zero_bytes(c);
  Hacl_SecretBox_ZeroPad_set_zero_bytes(subkey);
  return (uint32_t )0;
}

static uint32_t
Hacl_SecretBox_ZeroPad_crypto_secretbox_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t clen,
  uint8_t *n,
  uint8_t *k
)
{
  uint8_t subkey[32] = { 0 };
  uint8_t mackey[64] = { 0 };
  uint8_t cmac[16] = { 0 };
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(subkey, n, k);
  Salsa20_crypto_stream_salsa20(mackey, (uint64_t )32, n + (uint32_t )16, subkey);
  Poly1305_64_crypto_onetimeauth(cmac, c + (uint32_t )32, clen, mackey);
  uint8_t verify = Hacl_Policies_cmp_bytes(mac, cmac, (uint32_t )16);
  uint32_t z;
  if (verify == (uint8_t )0)
  {
    Salsa20_crypto_stream_salsa20_xor(m, c, clen + (uint64_t )32, n + (uint32_t )16, subkey);
    Hacl_SecretBox_ZeroPad_set_zero_bytes(subkey);
    Hacl_SecretBox_ZeroPad_set_zero_bytes(m);
    z = (uint32_t )0;
  }
  else
    z = (uint32_t )0xffffffff;
  return z;
}

static uint32_t
Hacl_SecretBox_ZeroPad_crypto_secretbox_easy(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  uint8_t cmac[16] = { 0 };
  uint32_t res = Hacl_SecretBox_ZeroPad_crypto_secretbox_detached(c, cmac, m, mlen, n, k);
  memcpy(c + (uint32_t )16, cmac, (uint32_t )16 * sizeof cmac[0]);
  return res;
}

static uint32_t
Hacl_SecretBox_ZeroPad_crypto_secretbox_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint64_t clen,
  uint8_t *n,
  uint8_t *k
)
{
  uint8_t *mac = c + (uint32_t )16;
  return
    Hacl_SecretBox_ZeroPad_crypto_secretbox_open_detached(m,
      c,
      mac,
      clen - (uint64_t )16,
      n,
      k);
}

static uint32_t Hacl_Box_ZeroPad_crypto_box_beforenm(uint8_t *k, uint8_t *pk, uint8_t *sk)
{
  uint8_t tmp[48] = { 0 };
  uint8_t *hsalsa_k = tmp;
  uint8_t *hsalsa_n = tmp + (uint32_t )32;
  Curve25519_crypto_scalarmult(hsalsa_k, sk, pk);
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(k, hsalsa_n, hsalsa_k);
  return (uint32_t )0;
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_detached_afternm(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  return Hacl_SecretBox_ZeroPad_crypto_secretbox_detached(c, mac, m, mlen, n, k);
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_detached(
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
  uint8_t *k = key;
  uint8_t *subkey = key + (uint32_t )32;
  uint8_t *hsalsa_n = key + (uint32_t )64;
  Curve25519_crypto_scalarmult(k, sk, pk);
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(subkey, hsalsa_n, k);
  uint32_t z = Hacl_SecretBox_ZeroPad_crypto_secretbox_detached(c, mac, m, mlen, n, subkey);
  return z;
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_open_detached(
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
  uint8_t *k = key;
  uint8_t *subkey = key + (uint32_t )32;
  uint8_t *hsalsa_n = key + (uint32_t )64;
  Curve25519_crypto_scalarmult(k, sk, pk);
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(subkey, hsalsa_n, k);
  uint32_t z = Hacl_SecretBox_ZeroPad_crypto_secretbox_open_detached(m, c, mac, mlen, n, subkey);
  return z;
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_easy_afternm(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  return Hacl_Box_ZeroPad_crypto_box_detached_afternm(c + (uint32_t )16, c, m, mlen, n, k);
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_easy(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
)
{
  uint8_t cmac[16] = { 0 };
  uint32_t res = Hacl_Box_ZeroPad_crypto_box_detached(c, cmac, m, mlen, n, pk, sk);
  memcpy(c + (uint32_t )16, cmac, (uint32_t )16 * sizeof cmac[0]);
  return res;
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
)
{
  uint8_t *mac = c + (uint32_t )16;
  return Hacl_Box_ZeroPad_crypto_box_open_detached(m, c, mac, mlen - (uint64_t )16, n, pk, sk);
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_open_detached_afternm(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  return Hacl_SecretBox_ZeroPad_crypto_secretbox_open_detached(m, c, mac, mlen, n, k);
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_open_easy_afternm(
  uint8_t *m,
  uint8_t *c,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  uint8_t *mac = c;
  uint8_t *c0 = c + (uint32_t )16;
  return
    Hacl_Box_ZeroPad_crypto_box_open_detached_afternm(m,
      c0,
      mac,
      mlen - (uint64_t )16,
      n,
      k);
}

Prims_int NaCl_crypto_box_NONCEBYTES;

Prims_int NaCl_crypto_box_PUBLICKEYBYTES;

Prims_int NaCl_crypto_box_SECRETKEYBYTES;

Prims_int NaCl_crypto_box_MACBYTES;

Prims_int NaCl_crypto_secretbox_NONCEBYTES;

Prims_int NaCl_crypto_secretbox_KEYBYTES;

Prims_int NaCl_crypto_secretbox_MACBYTES;

uint32_t
NaCl_crypto_secretbox_detached(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  return Hacl_SecretBox_ZeroPad_crypto_secretbox_detached(c, mac, m, mlen, n, k);
}

uint32_t
NaCl_crypto_secretbox_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t clen,
  uint8_t *n,
  uint8_t *k
)
{
  return Hacl_SecretBox_ZeroPad_crypto_secretbox_open_detached(m, c, mac, clen, n, k);
}

uint32_t
NaCl_crypto_secretbox_easy(uint8_t *c, uint8_t *m, uint64_t mlen, uint8_t *n, uint8_t *k)
{
  return Hacl_SecretBox_ZeroPad_crypto_secretbox_easy(c, m, mlen, n, k);
}

uint32_t
NaCl_crypto_secretbox_open_easy(uint8_t *m, uint8_t *c, uint64_t clen, uint8_t *n, uint8_t *k)
{
  return Hacl_SecretBox_ZeroPad_crypto_secretbox_open_easy(m, c, clen, n, k);
}

uint32_t NaCl_crypto_box_beforenm(uint8_t *k, uint8_t *pk, uint8_t *sk)
{
  return Hacl_Box_ZeroPad_crypto_box_beforenm(k, pk, sk);
}

uint32_t
NaCl_crypto_box_detached_afternm(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  return Hacl_Box_ZeroPad_crypto_box_detached_afternm(c, mac, m, mlen, n, k);
}

uint32_t
NaCl_crypto_box_detached(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
)
{
  return Hacl_Box_ZeroPad_crypto_box_detached(c, mac, m, mlen, n, pk, sk);
}

uint32_t
NaCl_crypto_box_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
)
{
  return Hacl_Box_ZeroPad_crypto_box_open_detached(m, c, mac, mlen, n, pk, sk);
}

uint32_t
NaCl_crypto_box_easy_afternm(uint8_t *c, uint8_t *m, uint64_t mlen, uint8_t *n, uint8_t *k)
{
  return Hacl_Box_ZeroPad_crypto_box_easy_afternm(c, m, mlen, n, k);
}

uint32_t
NaCl_crypto_box_easy(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
)
{
  return Hacl_Box_ZeroPad_crypto_box_easy(c, m, mlen, n, pk, sk);
}

uint32_t
NaCl_crypto_box_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
)
{
  return Hacl_Box_ZeroPad_crypto_box_open_easy(m, c, mlen, n, pk, sk);
}

uint32_t
NaCl_crypto_box_open_detached_afternm(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  return Hacl_Box_ZeroPad_crypto_box_open_detached_afternm(m, c, mac, mlen, n, k);
}

uint32_t
NaCl_crypto_box_open_easy_afternm(
  uint8_t *m,
  uint8_t *c,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  return Hacl_Box_ZeroPad_crypto_box_open_easy_afternm(m, c, mlen, n, k);
}

