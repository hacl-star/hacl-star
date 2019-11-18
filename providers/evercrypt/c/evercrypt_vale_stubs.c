#include <inttypes.h>
#include "kremlin/internal/target.h"

#if defined(_MSC_VER)  /* Visual Studio - always use __stdcall */
  #define STDCALL __stdcall
#elif defined(WIN32)   /* GCC/MinGW targeting Windows 32-bit - use the __stdcall macro */
  #define STDCALL __attribute__((stdcall))
#else                  /* Targeting other platforms - use the ambient calling convention */
  #define STDCALL
#endif

/* Real names from aes.asm */
extern void STDCALL KeyExpansionStdcall(const void *key_ptr, void *expanded_key_ptr, void *placeholder);
extern void STDCALL AES128EncryptOneBlockStdcall(void *output_ptr, const void *input_ptr, const void *expanded_key_ptr, void *placeholder);

/* From EverCrypt.Vale.fsti */
void aes128_key_expansion_sbox(uint8_t *k, uint8_t *w, uint8_t *sb)
{
  KeyExpansionStdcall(k, w, sb);
}

/* From EverCrypt.Vale.fsti */
void aes128_encrypt_one_block(uint8_t *out, uint8_t *in, uint8_t *w, uint8_t *sb)
{
  AES128EncryptOneBlockStdcall(out, in, w, sb);
}

#if !defined(_M_X64) && !defined(__x86_64__)
/* On non-x64 builds, define no-op stubs for Vale assembly code to avoid */
/* unresolved symbols while we wait for 32-bit Vale implementations. */
void __stdcall old_aes128_key_expansion(uint8_t *key_ptr, uint8_t *expanded_key_ptr)
{
    KRML_HOST_EPRINTF("Vale aes128_key_expansion() isn't implemented in this platform.  Do not call.\n");
    KRML_HOST_EXIT(255);
}

void __stdcall old_gcm128_encrypt(void *x0)
{
    KRML_HOST_EPRINTF("Vale gcm128_encrypt() isn't implemented in this platform.  Do not call.\n");
    KRML_HOST_EXIT(255);
}

void __stdcall old_gcm128_decrypt(void *x0)
{
    KRML_HOST_EPRINTF("Vale gcm128_decrypt() isn't implemented in this platform.  Do not call.\n");
    KRML_HOST_EXIT(255);
}

void __stdcall old_aes256_key_expansion(uint8_t *key_ptr, uint8_t *expanded_key_ptr)
{
    KRML_HOST_EPRINTF("Vale aes256_key_expansion() isn't implemented in this platform.  Do not call.\n");
    KRML_HOST_EXIT(255);
}

void __stdcall old_gcm256_encrypt(void *x0)
{
    KRML_HOST_EPRINTF("Vale gcm256_encrypt() isn't implemented in this platform.  Do not call.\n");
    KRML_HOST_EXIT(255);
}

void __stdcall old_gcm256_decrypt(void *x0)
{
    KRML_HOST_EPRINTF("Vale gcm256_decrypt() isn't implemented in this platform.  Do not call.\n");
    KRML_HOST_EXIT(255);
}
#endif
