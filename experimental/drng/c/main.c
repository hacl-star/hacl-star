#include <stdio.h>
#include <stdint.h>
#include "Hacl_Hardware_Intel_CPUID.h"

int intel_check_drng(){

  // Check if the processor is an Intel CPU
  if ( _is_intel_cpu()) {
    cpuid_t features;

    // Get the CPU information
    // Check for the RDRAND feature bit
    cpuid(&features, 1, 0);

    if (features.ecx & 0x40000000 == 0x40000000) {
      return 0;
    }
  }
  return 1;
}

int main () {

  if (intel_check_drng() == 0) {
    printf("Intel CPU with RDRAND feature Enabled !\n");
  } else {
    perror("This hardware does not support DRNG !\n");
  }
  return 0;
}
