#include "stdint.h"
#include "stdio.h"
#include "Spec_Lib_Print.h"

void Spec_Lib_Print_print_bytes(uint32_t len, uint8_t* buffer) {
  for (int i = 0; i < len; i++){
    printf("%02x ", buffer[i]);
  }
}

void Spec_Lib_Print_print_compare(uint32_t len, uint8_t* buffer1, uint8_t* buffer2) {
  for (int i = 0; i < len; i++){
    printf("%02x ", buffer1[i]);
  }
  printf("\n");
  for (int i = 0; i < len; i++){
    printf("%02x ", buffer2[i]);
  }
  printf("\n");
}
