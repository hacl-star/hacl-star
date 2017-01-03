#include "Hacl_Symmetric_XSalsa20.h"

void
Hacl_Symmetric_XSalsa20_crypto_stream_xsalsa20(
  uint8_t *c,
  uint64_t clen,
  uint8_t *n,
  uint8_t *k
)
{
  uint8_t subkey[32] = { 0 };
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(subkey, n + (uint32_t )0, k);
  Hacl_Symmetric_Salsa20_crypto_stream_salsa20(c, clen, n + (uint32_t )16, subkey);
}

void
Hacl_Symmetric_XSalsa20_crypto_stream_xsalsa20_xor_ic(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint64_t ic,
  uint8_t *k
)
{
  uint8_t subkey[32] = { 0 };
  Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(subkey, n + (uint32_t )0, k);
  Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic(c, m, mlen, n + (uint32_t )16, ic, subkey);
}

void
Hacl_Symmetric_XSalsa20_crypto_stream_xsalsa20_xor(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  Hacl_Symmetric_XSalsa20_crypto_stream_xsalsa20_xor_ic(c, m, mlen, n, (uint64_t )0, k);
  return;
}

