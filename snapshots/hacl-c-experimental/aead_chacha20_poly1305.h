#include "Chacha20.h"
#include "Poly1305_64.h"

void poly1305_key_gen(uint8_t* otk, uint8_t* key, uint8_t* nonce);

uint32_t hacl_aead_chacha20_poly1305_encrypt(uint8_t *plaintext,  uint32_t plaintext_len,
                                             uint8_t *aad,        uint32_t aad_len,
                                             uint8_t *key,        uint8_t *iv,
                                             uint8_t *ciphertext, uint8_t *tag);

uint32_t hacl_aead_chacha20_poly1305_decrypt(uint8_t *ciphertext, uint32_t ciphertext_len,
                                             uint8_t *aad,        uint32_t aad_len,
                                             uint8_t *tag,        uint8_t *key,
                                             uint8_t *iv,         uint8_t *plaintext);
