#include <stdint.h>
#include <stdlib.h>

#if defined(_MSC_VER)  // Visual Studio - always use __stdcall
  #define STDCALL __stdcall
#elif defined(WIN32)   // GCC/MinGW targeting Windows 32-bit - use the __stdcall macro
  #define STDCALL __attribute__((stdcall))
#else                  // Targeting other platforms - use the ambient calling convention
  #define STDCALL
#endif

extern void STDCALL KeyExpansionStdcall(const void *key_ptr, void *expanded_key_ptr, void *placeholder);
extern void STDCALL AES128EncryptOneBlockStdcall(void *output_ptr, const void *input_ptr, const void *expanded_key_ptr, void *placeholder);

void Vale_AES_keyExpansion(uint8_t *k, uint8_t *w, uint8_t *sb)
{
  KeyExpansionStdcall(k, w, sb);
}

void Vale_AES_cipher(uint8_t *out, uint8_t *in, uint8_t *w, uint8_t *sb)
{
  AES128EncryptOneBlockStdcall(out, in, w, sb);
}
