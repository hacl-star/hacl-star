#include "NaCl.h"

static void Hacl_SecretBox_ZeroPad_set_zero_bytes(uint8_t *b)
{
  uint8_t zero1 = (uint8_t )0;
  b[0] = zero1;
  b[1] = zero1;
  b[2] = zero1;
  b[3] = zero1;
  b[4] = zero1;
  b[5] = zero1;
  b[6] = zero1;
  b[7] = zero1;
  b[8] = zero1;
  b[9] = zero1;
  b[10] = zero1;
  b[11] = zero1;
  b[12] = zero1;
  b[13] = zero1;
  b[14] = zero1;
  b[15] = zero1;
  b[16] = zero1;
  b[17] = zero1;
  b[18] = zero1;
  b[19] = zero1;
  b[20] = zero1;
  b[21] = zero1;
  b[22] = zero1;
  b[23] = zero1;
  b[24] = zero1;
  b[25] = zero1;
  b[26] = zero1;
  b[27] = zero1;
  b[28] = zero1;
  b[29] = zero1;
  b[30] = zero1;
  b[31] = zero1;
}

static uint32_t
Hacl_SecretBox_ZeroPad_crypto_secretbox_detached(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *k1
)
{
  uint32_t mlen_ = (uint32_t )mlen;
  uint8_t subkey[32] = { 0 };
  Salsa20_hsalsa20(subkey, k1, n1);
  Salsa20_salsa20(c, m, mlen_ + (uint32_t )32, subkey, n1 + (uint32_t )16, (uint64_t )0);
  Poly1305_64_crypto_onetimeauth(mac, c + (uint32_t )32, mlen, c);
  Hacl_SecretBox_ZeroPad_set_zero_bytes(c);
  Hacl_SecretBox_ZeroPad_set_zero_bytes(subkey);
  return (uint32_t )0;
}

static uint32_t
Hacl_SecretBox_ZeroPad_crypto_secretbox_open_detached_decrypt(
  uint8_t *m,
  uint8_t *c,
  uint64_t clen,
  uint8_t *n1,
  uint8_t *subkey,
  uint8_t verify
)
{
  uint32_t clen_ = (uint32_t )clen;
  if (verify == (uint8_t )0)
  {
    Salsa20_salsa20(m, c, clen_ + (uint32_t )32, subkey, n1 + (uint32_t )16, (uint64_t )0);
    Hacl_SecretBox_ZeroPad_set_zero_bytes(subkey);
    Hacl_SecretBox_ZeroPad_set_zero_bytes(m);
    return (uint32_t )0;
  }
  else
    return (uint32_t )0xffffffff;
}

static uint32_t
Hacl_SecretBox_ZeroPad_crypto_secretbox_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t clen,
  uint8_t *n1,
  uint8_t *k1
)
{
  uint8_t tmp[112] = { 0 };
  uint8_t *subkey = tmp;
  uint8_t *mackey = tmp + (uint32_t )32;
  uint8_t *mackey_ = tmp + (uint32_t )64;
  uint8_t *cmac = tmp + (uint32_t )96;
  Salsa20_hsalsa20(subkey, k1, n1);
  Salsa20_salsa20(mackey, mackey_, (uint32_t )32, subkey, n1 + (uint32_t )16, (uint64_t )0);
  Poly1305_64_crypto_onetimeauth(cmac, c + (uint32_t )32, clen, mackey);
  uint8_t result = Hacl_Policies_cmp_bytes(mac, cmac, (uint32_t )16);
  uint8_t verify = result;
  uint32_t
  z =
    Hacl_SecretBox_ZeroPad_crypto_secretbox_open_detached_decrypt(m,
      c,
      clen,
      n1,
      subkey,
      verify);
  return z;
}

static uint32_t
Hacl_SecretBox_ZeroPad_crypto_secretbox_easy(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *k1
)
{
  uint8_t cmac[16] = { 0 };
  uint32_t res = Hacl_SecretBox_ZeroPad_crypto_secretbox_detached(c, cmac, m, mlen, n1, k1);
  memcpy(c + (uint32_t )16, cmac, (uint32_t )16 * sizeof cmac[0]);
  return res;
}

static uint32_t
Hacl_SecretBox_ZeroPad_crypto_secretbox_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint64_t clen,
  uint8_t *n1,
  uint8_t *k1
)
{
  uint8_t *mac = c;
  return Hacl_SecretBox_ZeroPad_crypto_secretbox_open_detached(m, c, mac, clen, n1, k1);
}

static uint32_t Hacl_Box_ZeroPad_crypto_box_beforenm(uint8_t *k1, uint8_t *pk, uint8_t *sk)
{
  uint8_t tmp[48] = { 0 };
  uint8_t *hsalsa_k = tmp;
  uint8_t *hsalsa_n = tmp + (uint32_t )32;
  Curve25519_crypto_scalarmult(hsalsa_k, sk, pk);
  Salsa20_hsalsa20(k1, hsalsa_k, hsalsa_n);
  return (uint32_t )0;
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_detached_afternm(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *k1
)
{
  return Hacl_SecretBox_ZeroPad_crypto_secretbox_detached(c, mac, m, mlen, n1, k1);
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_detached(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *pk,
  uint8_t *sk
)
{
  uint8_t key[80] = { 0 };
  uint8_t *k1 = key;
  uint8_t *subkey = key + (uint32_t )32;
  uint8_t *hsalsa_n = key + (uint32_t )64;
  Curve25519_crypto_scalarmult(k1, sk, pk);
  Salsa20_hsalsa20(subkey, k1, hsalsa_n);
  uint32_t z = Hacl_SecretBox_ZeroPad_crypto_secretbox_detached(c, mac, m, mlen, n1, subkey);
  return z;
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *pk,
  uint8_t *sk
)
{
  uint8_t key[80] = { 0 };
  uint8_t *k1 = key;
  uint8_t *subkey = key + (uint32_t )32;
  uint8_t *hsalsa_n = key + (uint32_t )64;
  Curve25519_crypto_scalarmult(k1, sk, pk);
  Salsa20_hsalsa20(subkey, k1, hsalsa_n);
  uint32_t
  z = Hacl_SecretBox_ZeroPad_crypto_secretbox_open_detached(m, c, mac, mlen, n1, subkey);
  return z;
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_easy_afternm(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *k1
)
{
  uint8_t cmac[16] = { 0 };
  uint32_t z = Hacl_Box_ZeroPad_crypto_box_detached_afternm(c, cmac, m, mlen, n1, k1);
  memcpy(c + (uint32_t )16, cmac, (uint32_t )16 * sizeof cmac[0]);
  return z;
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_easy(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *pk,
  uint8_t *sk
)
{
  uint8_t cmac[16] = { 0 };
  uint32_t res = Hacl_Box_ZeroPad_crypto_box_detached(c, cmac, m, mlen, n1, pk, sk);
  memcpy(c + (uint32_t )16, cmac, (uint32_t )16 * sizeof cmac[0]);
  return res;
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *pk,
  uint8_t *sk
)
{
  uint8_t *mac = c + (uint32_t )16;
  return Hacl_Box_ZeroPad_crypto_box_open_detached(m, c, mac, mlen, n1, pk, sk);
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_open_detached_afternm(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *k1
)
{
  return Hacl_SecretBox_ZeroPad_crypto_secretbox_open_detached(m, c, mac, mlen, n1, k1);
}

static uint32_t
Hacl_Box_ZeroPad_crypto_box_open_easy_afternm(
  uint8_t *m,
  uint8_t *c,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *k1
)
{
  uint8_t *mac = c;
  uint32_t t = Hacl_Box_ZeroPad_crypto_box_open_detached_afternm(m, c, mac, mlen, n1, k1);
  return t;
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
  uint8_t *n1,
  uint8_t *k1
)
{
  return Hacl_SecretBox_ZeroPad_crypto_secretbox_detached(c, mac, m, mlen, n1, k1);
}

uint32_t
NaCl_crypto_secretbox_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t clen,
  uint8_t *n1,
  uint8_t *k1
)
{
  return Hacl_SecretBox_ZeroPad_crypto_secretbox_open_detached(m, c, mac, clen, n1, k1);
}

uint32_t
NaCl_crypto_secretbox_easy(uint8_t *c, uint8_t *m, uint64_t mlen, uint8_t *n1, uint8_t *k1)
{
  return Hacl_SecretBox_ZeroPad_crypto_secretbox_easy(c, m, mlen, n1, k1);
}

uint32_t
NaCl_crypto_secretbox_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint64_t clen,
  uint8_t *n1,
  uint8_t *k1
)
{
  return Hacl_SecretBox_ZeroPad_crypto_secretbox_open_easy(m, c, clen, n1, k1);
}

uint32_t NaCl_crypto_box_beforenm(uint8_t *k1, uint8_t *pk, uint8_t *sk)
{
  return Hacl_Box_ZeroPad_crypto_box_beforenm(k1, pk, sk);
}

uint32_t
NaCl_crypto_box_detached_afternm(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *k1
)
{
  return Hacl_Box_ZeroPad_crypto_box_detached_afternm(c, mac, m, mlen, n1, k1);
}

uint32_t
NaCl_crypto_box_detached(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *pk,
  uint8_t *sk
)
{
  return Hacl_Box_ZeroPad_crypto_box_detached(c, mac, m, mlen, n1, pk, sk);
}

uint32_t
NaCl_crypto_box_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *pk,
  uint8_t *sk
)
{
  return Hacl_Box_ZeroPad_crypto_box_open_detached(m, c, mac, mlen, n1, pk, sk);
}

uint32_t
NaCl_crypto_box_easy_afternm(uint8_t *c, uint8_t *m, uint64_t mlen, uint8_t *n1, uint8_t *k1)
{
  return Hacl_Box_ZeroPad_crypto_box_easy_afternm(c, m, mlen, n1, k1);
}

uint32_t
NaCl_crypto_box_easy(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *pk,
  uint8_t *sk
)
{
  return Hacl_Box_ZeroPad_crypto_box_easy(c, m, mlen, n1, pk, sk);
}

uint32_t
NaCl_crypto_box_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *pk,
  uint8_t *sk
)
{
  return Hacl_Box_ZeroPad_crypto_box_open_easy(m, c, mlen, n1, pk, sk);
}

uint32_t
NaCl_crypto_box_open_detached_afternm(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *k1
)
{
  return Hacl_Box_ZeroPad_crypto_box_open_detached_afternm(m, c, mac, mlen, n1, k1);
}

uint32_t
NaCl_crypto_box_open_easy_afternm(
  uint8_t *m,
  uint8_t *c,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *k1
)
{
  return Hacl_Box_ZeroPad_crypto_box_open_easy_afternm(m, c, mlen, n1, k1);
}

