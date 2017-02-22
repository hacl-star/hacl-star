#include "Chacha20Poly1305.h"
void
Hacl_AEAD_Chacha20Poly1305_encrypt(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *aad,
  uint64_t aadlen,
  uint8_t *n,
  uint8_t *k
)
{
  uint32_t ctx[16] = { 0 };
  //uint32_t ctx[16] = { 0 };
  Hacl_Symmetric_Chacha20_chacha_keysetup(ctx, k);
  Hacl_Symmetric_Chacha20_chacha_ietf_ivsetup(ctx, n, 1);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes(ctx, m, c, mlen);

  uint8_t mackey[32] = {0};
  Hacl_Symmetric_Chacha20_chacha_keysetup(ctx, k);
  Hacl_Symmetric_Chacha20_chacha_ietf_ivsetup(ctx, n, 0);
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes(ctx, mackey, mackey, 64);

  uint64_t buf[6] = { 0 };
  uint64_t *r = buf;
  uint64_t *h = buf + (uint32_t )3;
  Hacl_Impl_Poly1305_64_poly1305_state st = { .x00 = r, .x01 = h };
  Hacl_Impl_Poly1305_64_mac_blocks_init(st, c, mlen, mackey);
  Hacl_Impl_Poly1305_64_mac_blocks_continue(st, aad, aadlen);
  uint8_t last[16];
  store64_le(last,aadlen);
  store64_le(last+16,mlen);
  Hacl_Impl_Poly1305_64_mac_blocks_finish(st, mac, last, 16, mackey);
  
  //Hacl_Impl_Poly1305_64_crypto_onetimeauth(mac, c, mlen, mackey);
}
