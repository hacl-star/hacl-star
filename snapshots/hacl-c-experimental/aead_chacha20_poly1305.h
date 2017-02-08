#include "Chacha20.h"
#include "Poly1305_64.h"

void blit(uint8_t* src, uint32_t len, uint8_t* dest, uint32_t pos);

void poly1305_key_gen(uint8_t* otk, uint8_t* key, uint8_t* nonce);

uint32_t hacl_aead_chacha20_poly1305_encrypt(uint8_t *plaintext,  uint32_t plaintext_len,
                                             uint8_t *aad,        uint32_t aad_len,
                                             uint8_t *key,        uint8_t *iv,
                                             uint8_t *ciphertext, uint8_t *tag);
