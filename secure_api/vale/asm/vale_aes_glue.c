#include <stdint.h>
#include <stdlib.h>

#if defined(_MSC_VER)  // Visual Studio - always use __stdcall
  #define STDCALL __stdcall
#elif defined(WIN32)   // GCC/MinGW targeting Windows 32-bit - use the __stdcall macro
  #define STDCALL __attribute__((stdcall))
#else                  // Targeting other platforms - use the ambient calling convention
  #define STDCALL
#endif

/*
typedef unsigned char byte;

typedef struct {
  byte* plain;
  uint64_t plain_len;
  byte* aad;
  uint64_t aad_len;
  byte* iv;
  byte* expanded_key;
  byte* cipher; // same length as plain
  byte *tag; // always 16 bytes
} gcm_args;
*/

extern void STDCALL KeyExpansionStdcall(const void *key_ptr, void *expanded_key_ptr, void *placeholder);
extern void STDCALL AES128EncryptOneBlockStdcall(void *output_ptr, const void *input_ptr, const void *expanded_key_ptr, void *placeholder);

/*
 * GCM support, WIP
 *
extern void aes_key_expansion(byte *key_ptr, byte *key_expansion_ptr);
extern void gcm_encrypt(gcm_args *a);
*/

void Vale_AES_keyExpansion(uint8_t *k, uint8_t *w, uint8_t *sb)
{
  KeyExpansionStdcall(k, w, sb);
}

void Vale_AES_cipher(uint8_t *out, uint8_t *in, uint8_t *w, uint8_t *sb)
{
  AES128EncryptOneBlockStdcall(out, in, w, sb);
}

/*
void Vale_AESGCM_key_expansion(uint8_t *key, uint8_t *xkey)
{
  aes_key_expansion(key, xkey);
}

void Vale_AESGCM_encrypt(uint8_t *xkey, uint8_t *plain, uint64_t plain_len,
  uint8_t *aad, uint64_t aad_len, uint8_t *iv, uint8_t *cipher, uint8_t *tag)
{
  gcm_args args;
  args.expanded_key = xkey;
  args.plain = plain;
  args.plain_len = plain_len;
  args.aad = aad;
  args.aad_len = aad_len;
  args.iv = iv;
  args.cipher = cipher;
  args.tag = tag;
  gcm_encrypt(&args);
}
*/

