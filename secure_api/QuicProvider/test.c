#include <sys/types.h>
#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include "mitlsffi.h"
#include "quic_provider.h"

void dump(unsigned char buffer[], size_t len)
{
  int i;
  for(i=0; i<len; i++) {
    printf("%02x",buffer[i]);
    if (i % 32 == 31 || i == len-1) printf("\n");
  }
}

int main(int argc, char **argv)
{
  char hash[64] = {0};
  char input[] = {};
  printf("SHA256('') =\n");
  quic_crypto_hash(TLS_hash_SHA256, hash, input, 0);
  dump(hash, 32);
  printf("\nSHA384('') = \n");
  quic_crypto_hash(TLS_hash_SHA384, hash, input, 0);
  dump(hash, 48);
  printf("\nSHA512('') = \n");
  quic_crypto_hash(TLS_hash_SHA512, hash, input, 0);
  dump(hash, 64);

  char *key = "Jefe";
  char *data = "what do ya want for nothing?";

  printf("\nHMAC-SHA256('Jefe', 'what do ya want for nothing?') = \n");
  quic_crypto_hmac(TLS_hash_SHA256, hash, key, 4, data, 28);
  dump(hash, 32);

  char *salt = "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c";
  char *ikm = "\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b";
  char *info = "\xf0\xf1\xf2\xf3\xf4\xf5\xf6\xf7\xf8\xf9";

  printf("\nprk = HKDF-EXTRACT-SHA256('0x000102030405060708090a0b0c', '0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b')\n");
  quic_crypto_hkdf_extract(TLS_hash_SHA256, hash, salt, 13, ikm, 22);
  dump(hash, 32);

  char prk[32] = {0};
  memcpy(prk, hash, 32);
  dump(prk, 32);

  char okm[42] = {0};
  printf("\nokm = HKDF-EXPAND-SHA256(prk, '0xf0f1f2f3f4f5f6f7f8f9', 42)\n");
  if(!quic_crypto_hkdf_expand(TLS_hash_SHA256, okm, 42, prk, 32, info, 10))
  {
    printf("Failed to call HKDF-expand\n");
    return 1;
  }
  dump(okm, 42);

  quic_secret s = {0};
  s.hash = TLS_hash_SHA256;
  s.ae = TLS_aead_AES_128_GCM;
  memcpy(s.secret, hash, 32);
  quic_crypto_tls_derive_secret(&s, &s, "EXPORTER-QUIC server 1-RTT Secret");

  quic_key* k;
  if(!quic_crypto_derive_key(&k, &s))
  {
    printf("Failed to derive key\n");
    return 1;
  }

  char cipher[128];
  printf("\nAES-128-GCM encrypt test:\n");
  quic_crypto_encrypt(k, cipher, 0, salt, 13, data, 28);
  dump(cipher, 28+16);

  if(quic_crypto_decrypt(k, hash, 0, salt, 13, cipher, 28+16)) {
    printf("DECRYPT SUCCES: \n");
    dump(hash, 28);
  } else {
    printf("DECRYPT FAILED.\n");
  }
  quic_crypto_free_key(k);

  s.hash = TLS_hash_SHA256;
  s.ae = TLS_aead_CHACHA20_POLY1305;

  if(!quic_crypto_derive_key(&k, &s))
  {
    printf("Failed to derive key\n");
    return 1;
  }

  printf("\nCHACHA20-POLY1305 encrypt test:\n");
  quic_crypto_encrypt(k, cipher, 0x29e255a7, salt, 13, data, 28);
  dump(cipher, 28+16);

  if(quic_crypto_decrypt(k, hash, 0x29e255a7, salt, 13, cipher, 28+16)) {
    printf("DECRYPT SUCCES: \n");
    dump(hash, 28);
  } else {
    printf("DECRYPT FAILED.\n");
  }

  quic_crypto_free_key(k);

  return 0;
}
