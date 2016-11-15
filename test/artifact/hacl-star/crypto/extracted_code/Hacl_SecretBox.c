#include "Hacl_SecretBox.h"

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
  uint8_t hsalsa_state[96] = { 0 };
  uint8_t *subkey = hsalsa_state + (uint32_t )0;
  uint8_t *block0 = hsalsa_state + (uint32_t )32;
  uint32_t zerobytes = (uint32_t )32;
  uint64_t zerobytes_64 = (uint64_t )zerobytes;
  uint64_t mlen0;
  if (mlen > (uint64_t )64 - zerobytes_64)
    mlen0 = (uint64_t )64 - zerobytes_64;
  else
    mlen0 = mlen;
  uint32_t mlen0_32 = (uint32_t )mlen0;
  memcpy(block0 + zerobytes, m, mlen0_32 * sizeof m[0]);
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(subkey, n + (uint32_t )0, k);
  Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor(block0,
    block0,
    mlen0 + zerobytes_64,
    n + (uint32_t )16,
    subkey);
  memcpy(c, block0 + zerobytes, mlen0_32 * sizeof block0[0]);
  if (mlen > mlen0)
    Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic(c + mlen0_32,
      m + mlen0_32,
      mlen - mlen0,
      n + (uint32_t )16,
      (uint64_t )1,
      subkey);
  Hacl_Symmetric_Poly1305_64_crypto_onetimeauth(mac, c, mlen, block0 + (uint32_t )0);
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
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(subkey, n + (uint32_t )0, k);
  Hacl_Symmetric_Salsa20_crypto_stream_salsa20(block0, (uint64_t )32, n + (uint32_t )16, subkey);
  Hacl_Symmetric_Poly1305_64_crypto_onetimeauth(tmp_mac, c, clen, block0 + (uint32_t )0);
  uint8_t verify = Hacl_Policies_cmp_bytes(mac, tmp_mac, (uint32_t )16);
  uint32_t zerobytes = (uint32_t )32;
  uint64_t zerobytes_64 = (uint64_t )32;
  uint64_t clen0;
  if (clen > (uint64_t )64 - zerobytes_64)
    clen0 = (uint64_t )64 - zerobytes_64;
  else
    clen0 = clen;
  uint32_t clen0_32 = (uint32_t )clen0;
  uint32_t z;
  if (verify == (uint8_t )0)
  {
    memcpy(block0 + zerobytes, c, clen0_32 * sizeof c[0]);
    Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor(block0,
      block0,
      zerobytes_64 + clen0,
      n + (uint32_t )16,
      subkey);
    memcpy(m, block0 + zerobytes, clen0_32 * sizeof block0[0]);
    if (clen > clen0)
      Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic(m + clen0_32,
        c + clen0_32,
        clen - clen0,
        n + (uint32_t )16,
        (uint64_t )1,
        subkey);
    z = (uint32_t )0x0;
  }
  else
    z = (uint32_t )0xffffffff;
  return z;
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
  uint8_t *c_ = c + (uint32_t )16;
  uint8_t *m_ = m + (uint32_t )0;
  uint8_t *mac = c + (uint32_t )0;
  return Hacl_SecretBox_crypto_secretbox_detached(c_, mac, m_, mlen, n, k);
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
  uint32_t clen_ = (uint32_t )(clen - (uint64_t )16);
  uint8_t *c_ = c + (uint32_t )16;
  uint8_t *mac = c + (uint32_t )0;
  return Hacl_SecretBox_crypto_secretbox_open_detached(m, c_, mac, clen - (uint64_t )16, n, k);
}

