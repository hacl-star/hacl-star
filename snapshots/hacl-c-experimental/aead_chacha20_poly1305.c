#include "Chacha20.h"
#include "Poly1305_64.h"

#include "aead_chacha20_poly1305.h"


#define AEAD_IV_LENGTH 12
#define AEAD_NONCE_LENGTH 16
#define POLY_OTK_LENGTH 32


void printHex(uint8_t* buf, uint32_t len){
  int i = 0;
  for (i = 0; i < len; i++) {
    printf("%02x", buf[i]);
  }
  printf("\n");
}

void blit(uint8_t* src, uint32_t len, uint8_t* dest, uint32_t pos){

  uint32_t i = 0;
  for (i = 0; i < len; i++){
    dest[i + pos] = src[i];
  }
}

void poly1305_key_gen(uint8_t* otk, uint8_t* key, uint8_t* nonce){

  // Allocate space for the output
  uint8_t output[64] = {0};

  // Allocate space for the chacha20 context
  uint32_t ctx_chacha[16];

  // Call the ChaCha20 block function
  Hacl_Symmetric_Chacha20_chacha_keysetup(ctx_chacha, key);
  Hacl_Symmetric_Chacha20_chacha_ietf_ivsetup(ctx_chacha, nonce, 0);
  Hacl_Symmetric_Chacha20_chacha20_update(ctx_chacha, output, output);

  // Return the first part of the output
  memcpy(otk, output, 32);
}


static const uint8_t _pad0[16] = { 0 };

uint32_t hacl_aead_chacha20_poly1305_encrypt(uint8_t *plaintext,  uint32_t plaintext_len,
                                             uint8_t *aad,        uint32_t aad_len,
                                             uint8_t *key,        uint8_t *iv,
                                             uint8_t *ciphertext, uint8_t *tag){

  // Store important information
  uint32_t _plaintext_len = plaintext_len;
  uint32_t _aad_len       = aad_len;

  // Allocate memory for the MAC one time key
  uint8_t otk[POLY_OTK_LENGTH];

  // Allocate integer for endianness conversions
  uint32_t slen = 0;

  // Generate the Poly 1305 one time key
  poly1305_key_gen(otk, key, iv);

  // Initialize the poly state for the MAC computation
  uint32_t ctx_chacha[16];

  // Prepare the ChaCha20 context
  Hacl_Symmetric_Chacha20_chacha_keysetup(ctx_chacha, key);
  Hacl_Symmetric_Chacha20_chacha_ietf_ivsetup(ctx_chacha, iv, 1);

  // Encrypt the plaintext using the symmetric cipher
  Hacl_Symmetric_Chacha20_chacha_encrypt_bytes(ctx_chacha, plaintext, ciphertext, plaintext_len);

  // Initialize the poly state for the MAC computation
  Hacl_Impl_Poly1305_64_poly1305_state ctx_poly;
  uint64_t ctxa[3];
  uint64_t ctxb[3];
  ctx_poly.x00 = (uint64_t*)ctxa;
  ctx_poly.x01 = (uint64_t*)ctxb;

  Hacl_Impl_Poly1305_64_poly1305_init_(ctx_poly, otk);

  // Process Additionnal data
  int i = 0;
  while (aad_len > 16){
    Hacl_Impl_Poly1305_64_poly1305_update(NULL, ctx_poly, aad + i * 16);
    aad_len -= 16;
    i++;
  }
  uint64_t aad_last[16] = {0};
  blit(aad + i * 16, aad_len, (uint8_t*)aad_last, 0);
  Hacl_Impl_Poly1305_64_poly1305_update(NULL, ctx_poly, (uint8_t*)aad_last);

  // Process Ciphertext
  i = 0;
  while (plaintext_len > 16){
    Hacl_Impl_Poly1305_64_poly1305_update(NULL, ctx_poly, ciphertext + i * 16);
    plaintext_len -= 16;
    i++;
  }
  uint64_t ciphertext_last[16] = {0};
  blit(ciphertext + i * 16, plaintext_len, (uint8_t*)ciphertext_last, 0);
  Hacl_Impl_Poly1305_64_poly1305_update(NULL, ctx_poly, (uint8_t*)ciphertext_last);

  // Process length
  uint8_t encodedlen[16];
  blit((uint8_t*)&_aad_len, 4, encodedlen, 0);
  blit((uint8_t*)&_plaintext_len, 4, encodedlen, 8);
  Hacl_Impl_Poly1305_64_poly1305_update(NULL, ctx_poly, encodedlen);

  // Finish the computation of the tag
  Hacl_Impl_Poly1305_64_poly1305_finish_(NULL, ctx_poly, tag, NULL, 0, otk+16);
}


/* uint32_t hacl_aead_chacha20_poly1305_decrypt(uint8_t *ciphertext, uint32_t ciphertext_len, uint8_t *aad, */
/*                                         uint32_t aad_len, uint8_t *tag, uint8_t *key, uint8_t *iv, */
/*                                         uint8_t *plaintext); */
