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
  uint64_t buf[6] = { 0 };
  uint64_t *r = buf;
  uint64_t *h = buf + (uint32_t )3;
  Hacl_Impl_Poly1305_64_poly1305_state st = { .x00 = r, .x01 = h };
  Poly1305_64_poly1305_blocks_init(st, aad, aadlen, mk);
  Poly1305_64_poly1305_blocks_continue(st, c, mlen);
  uint8_t lb[16] = { 0 };
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

/*   printf("[");for (int i = 0; i < 64; i++) printf("%d,",b[i]); printf("]\n"); */
/*   uint32_t mlen_ = (mlen % 16 == 0? mlen : mlen + (16 - mlen %16)); */
/*   uint32_t aadlen_ = (aadlen % 16 == 0? aadlen : aadlen + (16 - aadlen %16)); */
/*   uint32_t to_mac_len = mlen_ + aadlen_ + 16; */
/*   uint8_t* to_mac = malloc(to_mac_len); */
/*   for (int i = 0; i < to_mac_len; i++) to_mac[i] = 0; */
/*   memcpy(to_mac,aad,aadlen); */
/*   memcpy(to_mac+aadlen_,c,mlen); */
/*   printf("here: mlen %d, aadlen %d, mlen_ %d, aadlen_ %d \n",mlen,aadlen,mlen_,aadlen_);fflush(stdout); */
/*   store64_le(to_mac+aadlen_+mlen_,(uint64_t)aadlen); */
/*   store64_le(to_mac+aadlen_+mlen_+8,(uint64_t)mlen); */
/*   printf("[");  for (int i = 0; i < to_mac_len; i++) printf("%d; ",to_mac[i]); printf("]\n"); */
/*   Poly1305_64_crypto_onetimeauth(mac,to_mac,to_mac_len,b); */
/*   free(to_mac); */

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
  uint64_t buf[6] = { 0 };
  uint64_t *r = buf;
  uint64_t *h = buf + (uint32_t )3;
  Hacl_Impl_Poly1305_64_poly1305_state st = { .x00 = r, .x01 = h };
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

