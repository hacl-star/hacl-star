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
  printf("SHA256('') = ");
  quic_crypto_hash(TLS_hash_SHA256, hash, "", 0);
  dump(hash, 32);
  assert(!memcmp(hash, "\xe3\xb0\xc4\x42\x98\xfc\x1c\x14\x9a\xfb\xf4\xc8\x99\x6f\xb9\x24\x27\xae\x41\xe4\x64\x9b\x93\x4c\xa4\x95\x99\x1b\x78\x52\xb8\x55", 32));
  printf("\nSHA384('') = ");
  quic_crypto_hash(TLS_hash_SHA384, hash, "", 0);
  dump(hash, 48);
  assert(!memcmp(hash, "\x38\xb0\x60\xa7\x51\xac\x96\x38\x4c\xd9\x32\x7e\xb1\xb1\xe3\x6a\x21\xfd\xb7\x11\x14\xbe\x07\x43\x4c\x0c\xc7\xbf\x63\xf6\xe1\xda\x27\x4e\xde\xbf\xe7\x6f\x65\xfb\xd5\x1a\xd2\xf1\x48\x98\xb9\x5b", 48));
  printf("\nSHA512('') = ");
  quic_crypto_hash(TLS_hash_SHA512, hash, "", 0);
  dump(hash, 64);
  assert(!memcmp(hash, "\xcf\x83\xe1\x35\x7e\xef\xb8\xbd\xf1\x54\x28\x50\xd6\x6d\x80\x07\xd6\x20\xe4\x05\x0b\x57\x15\xdc\x83\xf4\xa9\x21\xd3\x6c\xe9\xce\x47\xd0\xd1\x3c\x5d\x85\xf2\xb0\xff\x83\x18\xd2\x87\x7e\xec\x2f\x63\xb9\x31\xbd\x47\x41\x7a\x81\xa5\x38\x32\x7a\xf9\x27\xda\x3e", 64));

  char *key = "Jefe";
  char *data = "what do ya want for nothing?";

  printf("\nHMAC-SHA256('Jefe', 'what do ya want for nothing?') = \n");
  quic_crypto_hmac(TLS_hash_SHA256, hash, key, 4, data, 28);
  dump(hash, 32);
  assert(!memcmp(hash, "\x5b\xdc\xc1\x46\xbf\x60\x75\x4e\x6a\x04\x24\x26\x08\x95\x75\xc7\x5a\x00\x3f\x08\x9d\x27\x39\x83\x9d\xec\x58\xb9\x64\xec\x38\x43", 32));

  printf("\nHMAC-SHA384('Jefe', 'what do ya want for nothing?') = \n");
  quic_crypto_hmac(TLS_hash_SHA384, hash, key, 4, data, 28);
  dump(hash, 48);
  assert(!memcmp(hash, "\xaf\x45\xd2\xe3\x76\x48\x40\x31\x61\x7f\x78\xd2\xb5\x8a\x6b\x1b\x9c\x7e\xf4\x64\xf5\xa0\x1b\x47\xe4\x2e\xc3\x73\x63\x22\x44\x5e\x8e\x22\x40\xca\x5e\x69\xe2\xc7\x8b\x32\x39\xec\xfa\xb2\x16\x49", 48));

  printf("\nHMAC-SHA512('Jefe', 'what do ya want for nothing?') = \n");
  quic_crypto_hmac(TLS_hash_SHA512, hash, key, 4, data, 28);
  dump(hash, 64);
  assert(!memcmp(hash, "\x16\x4b\x7a\x7b\xfc\xf8\x19\xe2\xe3\x95\xfb\xe7\x3b\x56\xe0\xa3\x87\xbd\x64\x22\x2e\x83\x1f\xd6\x10\x27\x0c\xd7\xea\x25\x05\x54\x97\x58\xbf\x75\xc0\x5a\x99\x4a\x6d\x03\x4f\x65\xf8\xf0\xe6\xfd\xca\xea\xb1\xa3\x4d\x4a\x6b\x4b\x63\x6e\x07\x0a\x38\xbc\xe7\x37", 64));

  char *salt = "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c";
  char *ikm = "\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b";
  char *info = "\xf0\xf1\xf2\xf3\xf4\xf5\xf6\xf7\xf8\xf9";

  printf("\nprk = HKDF-EXTRACT-SHA256('0x000102030405060708090a0b0c', '0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b')\n");
  quic_crypto_hkdf_extract(TLS_hash_SHA256, hash, salt, 13, ikm, 22);
  dump(hash, 32);
  assert(!memcmp(hash, "\x07\x77\x09\x36\x2c\x2e\x32\xdf\x0d\xdc\x3f\x0d\xc4\x7b\xba\x63\x90\xb6\xc7\x3b\xb5\x0f\x9c\x31\x22\xec\x84\x4a\xd7\xc2\xb3\xe5", 32));

  char okm[42] = {0};
  printf("\nokm = HKDF-EXPAND-SHA256(prk, '0xf0f1f2f3f4f5f6f7f8f9', 42)\n");
  if(!quic_crypto_hkdf_expand(TLS_hash_SHA256, okm, 42, hash, 32, info, 10))
  {
    printf("Failed to call HKDF-expand\n");
    return 1;
  }
  dump(okm, 42);
  assert(!memcmp(okm, "\x3c\xb2\x5f\x25\xfa\xac\xd5\x7a\x90\x43\x4f\x64\xd0\x36\x2f\x2a\x2d\x2d\x0a\x90\xcf\x1a\x5a\x4c\x5d\xb0\x2d\x56\xec\xc4\xc5\xbf\x34\x00\x72\x08\xd5\xb8\x87\x18\x58\x65", 42));

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

  assert(quic_crypto_decrypt(k, hash, 0, salt, 13, cipher, 28+16));
  assert(!memcmp(data, hash, 28));
  printf("DECRYPT SUCCES: ");
  dump(hash, 28);

  quic_crypto_free_key(k);
  s.hash = TLS_hash_SHA384;
  s.ae = TLS_aead_CHACHA20_POLY1305;

  assert(quic_crypto_derive_key(&k, &s));

  printf("\nCHACHA20-POLY1305 encrypt test:\n");
  assert(quic_crypto_encrypt(k, cipher, 0x29e255a7, salt, 13, data, 28));
  dump(cipher, 28+16);

  assert(quic_crypto_decrypt(k, hash, 0x29e255a7, salt, 13, cipher, 28+16));
  assert(!memcmp(data, hash, 28));
  printf("DECRYPT SUCCES: ");
  dump(hash, 28);

  quic_crypto_free_key(k);
  return 0;
}
