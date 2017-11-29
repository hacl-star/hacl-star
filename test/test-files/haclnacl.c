#include "haclnacl.h"
#include "kremlib.h"
#include "Hacl_Curve25519.h"
#include "Hacl_Chacha20.h"
#include "Hacl_Salsa20.h"
#define Hacl_Impl_Poly1305_64_State_poly1305_state Hacl_Impl_Poly1305_64_State_poly1305_state_poly
#include "Hacl_Poly1305_64.h"
#undef Hacl_Impl_Poly1305_64_State_poly1305_state
#define Hacl_Impl_Poly1305_64_State_poly1305_state Hacl_Impl_Poly1305_64_State_poly1305_state_aead
#include "Hacl_Chacha20Poly1305.h"
#undef Hacl_Impl_Poly1305_64_State_poly1305_state

#define K___uint32_t_uint8_t_ K___uint32_t_uint8_t_ed
#include "Hacl_Ed25519.h"
#undef K___uint32_t_uint8_t_
#define K___uint32_t_uint8_t_ K___uint32_t_uint8_t_sha256
#include "Hacl_SHA2_256.h"
#undef K___uint32_t_uint8_t_
#define K___uint32_t_uint8_t_ K___uint32_t_uint8_t_sha512
#include "Hacl_SHA2_512.h"
#undef K___uint32_t_uint8_t_
#include "NaCl.h"

extern void randombytes(uint8_t *bytes, uint64_t bytes_len);

void curve25519_scalarmult(uint8_t *out, uint8_t *secret, uint8_t *point){
  Hacl_Curve25519_crypto_scalarmult(out, secret, point);
}

void
chacha20(
         uint8_t *output,
         uint8_t *plain,
         uint32_t plain_len,
         uint8_t *key,
         uint8_t *nonce,
         uint32_t ctr
         ){
  Hacl_Chacha20_chacha20(output, plain, plain_len, key, nonce, ctr);
}

void
salsa20(
        uint8_t *output,
        uint8_t *plain,
        uint32_t len,
        uint8_t *key,
        uint8_t *nonce,
        uint64_t ctr
        ){
  Hacl_Salsa20_salsa20(output, plain, len, key, nonce, ctr);
}

void
poly1305_onetimeauth(uint8_t *output, uint8_t *input, uint64_t input_len, uint8_t *key){
  Hacl_Poly1305_64_crypto_onetimeauth(output, input, input_len, key);
}

uint32_t
aead_chacha20_poly1305_encrypt(
                               uint8_t *cipher,
                               uint8_t *mac,
                               uint8_t *msg,
                               uint32_t msg_len,
                               uint8_t *aad,
                               uint32_t aad_len,
                               uint8_t *key,
                               uint8_t *nonce
                               ){
  return Hacl_Chacha20Poly1305_aead_encrypt(cipher, mac, msg, msg_len, aad, aad_len, key, nonce);
}

uint32_t
aead_chacha20_poly1305_decrypt(
  uint8_t *msg,
  uint8_t *cipher,
  uint32_t msg_len,
  uint8_t *mac,
  uint8_t *aad,
  uint32_t aad_len,
  uint8_t *key,
  uint8_t *nonce
)
{
  return Hacl_Chacha20Poly1305_aead_decrypt(msg, cipher, msg_len, mac, aad, aad_len, key, nonce);
}

void ed25519_secret_to_public(uint8_t *public_key, uint8_t *secret_key){
  Hacl_Ed25519_secret_to_public(public_key, secret_key);
}

void ed25519_sign(uint8_t *signature, uint8_t *secret, uint8_t *msg, uint32_t msg_len){
  Hacl_Ed25519_sign(signature, secret, msg, msg_len);
}

bool ed25519_verify(uint8_t *public, uint8_t *msg, uint32_t msg_len, uint8_t *signature){
  return Hacl_Ed25519_verify(public, msg, msg_len, signature);
}

void sha2_512_hash(uint8_t *hash, uint8_t *input, uint32_t len){
  Hacl_SHA2_512_hash(hash, input, len);
}


/* NaCl-like API */
int
crypto_onetimeauth(uint8_t *output, uint8_t *input, uint64_t input_len, uint8_t *key){
  poly1305_onetimeauth(output, input, input_len, key);
  return 0;
}

int
crypto_onetimeauth_verify(uint8_t *auth, uint8_t *msg, uint64_t msg_len, uint8_t *key){
  uint8_t tag[16], tmp = 0xff;
  poly1305_onetimeauth(tag, msg, msg_len, key);
  for (int i = 0; i < 16; i++){
    tmp = tmp & FStar_UInt8_eq_mask(tag[i], auth[i]);
  }
  tmp >>= 7;
  return (int)tmp - 1;
}

int crypto_box_keypair(unsigned char *pk, unsigned char *sk){
  randombytes(sk, 32);
  uint8_t basepoint[32] = {9};
  curve25519_scalarmult(pk, sk, basepoint);
  return 0;
}

int crypto_box_easy(unsigned char *c, const unsigned char *m,
                    unsigned long long mlen, const unsigned char *n,
                    const unsigned char *pk, const unsigned char *sk){
  return NaCl_crypto_box_easy(c, (uint8_t*)m, mlen, (uint8_t*)n, (uint8_t*)pk, (uint8_t*)sk);
}

int crypto_box_open_easy(unsigned char *m, const unsigned char *c,
                         unsigned long long clen, const unsigned char *n,
                         const unsigned char *pk, const unsigned char *sk){
  return NaCl_crypto_box_open_easy(m, (uint8_t*)c, clen, (uint8_t*)n, (uint8_t*)pk, (uint8_t*)sk);
}

int crypto_box_beforenm(unsigned char *k, const unsigned char *pk,
                        const unsigned char *sk){
  return NaCl_crypto_box_beforenm(k, (uint8_t*)pk, (uint8_t*)sk);
}

int crypto_box_easy_afternm(unsigned char *c, const unsigned char *m,
                            unsigned long long mlen, const unsigned char *n,
                            const unsigned char *k){
  return NaCl_crypto_box_easy_afternm(c, (uint8_t*)m, mlen, (uint8_t*)n, (uint8_t*)k);
}

int crypto_box_open_easy_afternm(unsigned char *m, const unsigned char *c,
                                 unsigned long long clen, const unsigned char *n,
                                 const unsigned char *k){
  return NaCl_crypto_box_open_easy_afternm(m, (uint8_t*)c, clen, (uint8_t*)n, (uint8_t*)k);
}

int crypto_scalarmult_base(unsigned char *q, const unsigned char *n){
  /* This leaves room for improvements with precomputations */
  uint8_t basepoint[32] = {9};
  Hacl_Curve25519_crypto_scalarmult(q, (uint8_t*)n, basepoint);
  return 0;
}

int crypto_scalarmult(unsigned char *q, const unsigned char *n,
                      const unsigned char *p){
  Hacl_Curve25519_crypto_scalarmult(q, (uint8_t*)n, (uint8_t*)p);
  return 0;
}

uint32_t
crypto_secretbox_detached(
                          uint8_t *c,
                          uint8_t *mac,
                          uint8_t *m,
                          uint64_t mlen,
                          uint8_t *n,
                          uint8_t *k){
  return NaCl_crypto_secretbox_detached(c, mac, m, mlen, n, k);
}

uint32_t
crypto_secretbox_open_detached(
                               uint8_t *m,
                               uint8_t *c,
                               uint8_t *mac,
                               uint64_t clen,
                               uint8_t *n,
                               uint8_t *k
                               ){
  return NaCl_crypto_secretbox_open_detached(m, c, mac, clen, n, k);
}

uint32_t
crypto_secretbox_easy(uint8_t *c, uint8_t *m, uint64_t mlen, uint8_t *n, uint8_t *k){
  return NaCl_crypto_secretbox_easy(c, m, mlen, n, k);
}

uint32_t
crypto_secretbox_open_easy(
                           uint8_t *m,
                           uint8_t *c,
                           uint64_t clen,
                           uint8_t *n,
                           uint8_t *k){
  return NaCl_crypto_secretbox_open_easy(m, c, clen, n, k);
}

uint32_t
crypto_box_detached_afternm(
                            uint8_t *c,
                            uint8_t *mac,
                            uint8_t *m,
                            uint64_t mlen,
                            uint8_t *n,
                            uint8_t *k){
  return NaCl_crypto_box_detached_afternm(c, mac, m, mlen, n, k);
}

uint32_t
crypto_box_detached(
                    uint8_t *c,
                    uint8_t *mac,
                    uint8_t *m,
                    uint64_t mlen,
                    uint8_t *n,
                    uint8_t *pk,
                    uint8_t *sk){
  return NaCl_crypto_box_detached(c, mac, m, mlen, n, pk, sk);
}

uint32_t
crypto_box_open_detached(
                              uint8_t *m,
                              uint8_t *c,
                              uint8_t *mac,
                              uint64_t mlen,
                              uint8_t *n,
                              uint8_t *pk,
                              uint8_t *sk){
  return NaCl_crypto_box_open_detached(m, c, mac, mlen, n, pk, sk);
}

uint32_t
crypto_box_open_detached_afternm(
                                 uint8_t *m,
                                 uint8_t *c,
                                 uint8_t *mac,
                                 uint64_t mlen,
                                 uint8_t *n,
                                 uint8_t *k){
  return NaCl_crypto_box_detached_afternm(m, c, mac, mlen, n, k);
}

int
crypto_sign(
            uint8_t *signed_msg,
            long long unsigned int *signed_len,
            uint8_t *msg,
            uint64_t msg_len,
            uint8_t *sk
            ){
  Hacl_Ed25519_sign(signed_msg, sk, msg, msg_len);
  memmove(signed_msg+64, msg, msg_len * sizeof(uint8_t));
  *signed_len = msg_len + 64;
  return 0;
}

int crypto_sign_open(
                     uint8_t *unsigned_msg,
                     long long unsigned int *unsigned_msg_len,
                     uint8_t *msg,
                     uint64_t msg_len,
                     uint8_t *pk
                     ){
  uint32_t res;
  res = Hacl_Ed25519_verify(pk, msg+64, msg_len - 64, msg);
  if (res == true){
    memmove(unsigned_msg, msg+64, sizeof(uint8_t) * (msg_len-64));
    *unsigned_msg_len = msg_len - 64;
    return true;
  } else {
    return false;
  }
}

int crypto_sign_keypair(
                        uint8_t pk[32],
                        uint8_t sk[64]
                        ){
  randombytes(sk, 32 * sizeof(uint8_t));
  Hacl_Ed25519_secret_to_public(pk, sk);
  for (int i = 0; i < 32; i++) sk[32+i] = pk[i];
  return 0;
}

int crypto_sign_secret_to_public(uint8_t *public_key, uint8_t *secret_key){
  Hacl_Ed25519_secret_to_public(public_key, secret_key);
  return 0;
}

int crypto_box(uint8_t *cipher, uint8_t *msg, uint64_t msg_len, uint8_t *nonce, uint8_t *pk, uint8_t *sk){
  return crypto_box_easy(cipher, msg, msg_len - 32, nonce, pk, sk);
}

int crypto_box_open(uint8_t *msg, uint8_t *cipher, uint64_t cipher_len, uint8_t *nonce, uint8_t *pk, uint8_t *sk){
  return crypto_box_open_easy(msg, cipher, cipher_len - 32, nonce, pk, sk);
}

int crypto_box_afternm(uint8_t *cipher, uint8_t *msg, uint64_t msg_len, uint8_t *nonce, uint8_t *key){
  return NaCl_crypto_box_easy_afternm(cipher, msg, msg_len, nonce, key);
}

int crypto_box_open_afternm(uint8_t *msg, uint8_t *cipher, uint64_t cipher_len, uint8_t *nonce, uint8_t *key){
  return NaCl_crypto_box_open_easy_afternm(msg, cipher, cipher_len, nonce, key);
}

int crypto_secretbox(uint8_t *cipher, uint8_t *msg, uint64_t msg_len, uint8_t *nonce, uint8_t *key){
  return crypto_secretbox_easy(cipher, msg, msg_len - 32, nonce, key);
}

int crypto_secretbox_open(uint8_t *msg, uint8_t *cipher, uint64_t cipher_len, uint8_t *nonce, uint8_t *key){
  return crypto_secretbox_open_detached(msg, cipher, cipher + 16, cipher_len - 32, nonce, key);
}

int crypto_stream(uint8_t *cipher, uint64_t cipher_len, uint8_t *nonce, uint8_t *key){
  uint8_t subkey[32];
  memset(cipher, 0, cipher_len * sizeof(uint8_t));
  Hacl_Salsa20_hsalsa20(subkey, key, nonce);
  Hacl_Salsa20_salsa20(cipher, cipher, cipher_len, subkey, nonce + 16, 0);
  return 0;
}

int crypto_stream_xor(uint8_t *cipher, uint8_t *msg, uint64_t cipher_len, uint8_t *nonce, uint8_t *key){
  uint8_t subkey[32];
  memset(cipher, 0, cipher_len * sizeof(uint8_t));
  Hacl_Salsa20_hsalsa20(subkey, key, nonce);
  Hacl_Salsa20_salsa20(cipher, msg, cipher_len, subkey, nonce + 16, 0);
  return 0;
}


