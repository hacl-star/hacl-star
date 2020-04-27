#include <sys/auxv.h>
#include <asm/hwcap.h>

#include "EverCrypt_Arm.h"

bool EverCrypt_Arm_check_neon() {
  long hwcaps = getauxval(AT_HWCAP);
  return hwcaps & HWCAP_NEON;
}
