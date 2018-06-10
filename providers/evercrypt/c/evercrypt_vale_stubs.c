#include <inttypes.h>
#include "kremlin/internal/target.h"


#if !defined(_M_X64) && !defined(__x86_64__)
// On non-x64 builds, define no-op stubs for Vale assembly code to avoid
// unresolved symbols while we wait for 32-bit Vale implementations.
void __stdcall gcm_encrypt(void *x0)
{
    KRML_HOST_EPRINTF("Vale gcm_encrypt() isn't implemented in this platform.  Do not call.\n");
    KRML_HOST_EXIT(255);
}

void
__stdcall
sha256_main_i_SHA256_Compute64Steps(
  uint32_t *x0,
  uint32_t *x1,
  uint32_t x2,
  uint32_t x3,
  uint32_t x4,
  uint32_t x5,
  uint32_t x6,
  uint32_t x7,
  uint32_t x8,
  uint32_t x9,
  uint32_t x10,
  uint32_t x11,
  uint32_t x12,
  uint32_t x13,
  uint32_t x14,
  uint32_t x15,
  uint32_t x16,
  uint32_t x17,
  uint32_t x18
)
{
    KRML_HOST_EPRINTF("Vale sha256_main_i_SHA256_Compute64Steps() isn't implemented in this platform.  Do not call.\n");
    KRML_HOST_EXIT(255);
}

void
__stdcall
sha256_main_i_SHA256_ComputeInitialWs(
  uint8_t *x0,
  uint32_t x1,
  uint32_t *x2,
  uint32_t x3,
  uint32_t x4,
  uint32_t x5,
  uint32_t x6
)
{
    KRML_HOST_EPRINTF("Vale sha256_main_i_SHA256_Compute64Steps() isn't implemented in this platform.  Do not call.\n");
    KRML_HOST_EXIT(255);
}
#endif
