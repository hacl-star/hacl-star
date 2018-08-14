/********************************************************************************************
* Functions for AES
*
* If USE_OPENSSL flag is defined it uses OpenSSL's AES implementation. 
* Otherwise, it uses a standalone implementation
*********************************************************************************************/

#include <assert.h>
#include <string.h>
#include "aes.h"
#include "aes_local.h"


#ifndef USE_OPENSSL

void AES128_load_schedule(const uint8_t *key, uint8_t *schedule) {
    aes128_load_schedule_c(key, schedule);
}


static inline void aes128_enc(const uint8_t *plaintext, const void *schedule, uint8_t *ciphertext) {
    aes128_enc_c(plaintext, schedule, ciphertext);
}
     

void AES128_ECB_enc_sch(const uint8_t *plaintext, const size_t plaintext_len, const void *schedule, uint8_t *ciphertext) {
    assert(plaintext_len % 16 == 0);
    for (size_t block = 0; block < plaintext_len / 16; block++) {
        aes128_enc(plaintext + (16 * block), schedule, ciphertext + (16 * block));
    }
}


void AES128_free_schedule(void *schedule) {
    memset(schedule, 0, 16*11);
}


void AES256_load_schedule(const uint8_t *key, uint8_t *schedule) {
    aes256_load_schedule_c(key, schedule);
}


static inline void aes256_enc(const uint8_t *plaintext, const void *schedule, uint8_t *ciphertext) {
    aes256_enc_c(plaintext, schedule, ciphertext);
}
     

void AES256_ECB_enc_sch(const uint8_t *plaintext, const size_t plaintext_len, const void *schedule, uint8_t *ciphertext) {
    assert(plaintext_len % 16 == 0);
    for (size_t block = 0; block < plaintext_len / 16; block++) {
        aes256_enc(plaintext + (16 * block), schedule, ciphertext + (16 * block));
    }
}


void AES256_free_schedule(void *schedule) {
    memset(schedule, 0, 16*15);
}

#else  // Use OpenSSL's AES implementation

void handleErrors(void)
{
    ERR_print_errors_fp(stderr);
    abort();
}


void AES128_free_schedule(EVP_CIPHER_CTX *schedule) {
    EVP_CIPHER_CTX_free(schedule);
}


void AES256_free_schedule(EVP_CIPHER_CTX *schedule) {
    EVP_CIPHER_CTX_free(schedule);
}


#endif
