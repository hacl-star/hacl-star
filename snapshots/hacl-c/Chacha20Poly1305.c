#include "Chacha20Poly1305.h"

Prims_int Chacha20Poly1305_noncelen;

Prims_int Chacha20Poly1305_keylen;

Prims_int Chacha20Poly1305_maclen;

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
  Chacha20_chacha20(c, m, mlen, k, n, (uint32_t )1);
  uint8_t b[64] = { 0 };
  Chacha20_chacha20_key_block(b, k, n, (uint32_t )0);
  uint8_t *mk = b;
  uint8_t *key_s = mk + (uint32_t )16;
  uint64_t buf[2];
  Poly1305_64_state st;
  st.x00 = buf;
  st.x01 = buf+1;
  uint8_t lb[16] = { 0 };
  Poly1305_64_poly1305_blocks_init(st, aad, aadlen, mk);
  Poly1305_64_poly1305_blocks_continue(st, c, mlen);
  uint8_t *x0 = lb;
  /* start inlining Hacl.Endianness.hstore64_le */
  /* start inlining Hacl.Endianness.store64_le */
  store64_le(x0, (uint64_t )aadlen);
  /* end inlining Hacl.Endianness.store64_le */
  /* end inlining Hacl.Endianness.hstore64_le */
  uint8_t *x00 = lb + (uint32_t )8;
  /* start inlining Hacl.Endianness.hstore64_le */
  /* start inlining Hacl.Endianness.store64_le */
  store64_le(x00, (uint64_t )mlen);
  /* end inlining Hacl.Endianness.store64_le */
  /* end inlining Hacl.Endianness.hstore64_le */
  Poly1305_64_poly1305_blocks_finish(st, lb, mac, key_s);
  return (uint32_t )0;
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
  uint8_t b[64] = { 0 };
  Chacha20_chacha20_key_block(b, k, n, (uint32_t )0);
  uint8_t *mk = b;
  uint8_t *key_s = mk + (uint32_t )16;
  uint8_t rmac[16] = { 0 };
  uint64_t buf[2];
  Poly1305_64_state st;
  st.x00 = buf;
  st.x01 = buf+1;
  uint8_t lb[16] = { 0 };
  Poly1305_64_poly1305_blocks_init(st, aad, aadlen, mk);
  Poly1305_64_poly1305_blocks_continue(st, c, mlen);
  uint8_t *x0 = lb;
  /* start inlining Hacl.Endianness.hstore64_le */
  /* start inlining Hacl.Endianness.store64_le */
  store64_le(x0, (uint64_t )aadlen);
  /* end inlining Hacl.Endianness.store64_le */
  /* end inlining Hacl.Endianness.hstore64_le */
  uint8_t *x00 = lb + (uint32_t )8;
  /* start inlining Hacl.Endianness.hstore64_le */
  /* start inlining Hacl.Endianness.store64_le */
  store64_le(x00, (uint64_t )mlen);
  /* end inlining Hacl.Endianness.store64_le */
  /* end inlining Hacl.Endianness.hstore64_le */
  Poly1305_64_poly1305_blocks_finish(st, lb, rmac, key_s);
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

