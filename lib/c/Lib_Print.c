#include "stdint.h"
#include "stdio.h"
#include "Lib_Print.h"

void Lib_Print_print_bytes(uint32_t len, uint8_t* buffer) {
  for (int i = 0; i < len; i++){
    printf("%02x ", buffer[i]);
  }
  printf("\n");
}

void Lib_Print_print_compare(uint32_t len, uint8_t* buffer1, uint8_t* buffer2) {
  for (int i = 0; i < len; i++){
    printf("%02x ", buffer1[i]);
  }
  printf("\n");
  for (int i = 0; i < len; i++){
    printf("%02x ", buffer2[i]);
  }
  printf("\n");
}

void Lib_Print_print_compare_display(uint32_t len, uint8_t* buffer1, uint8_t* buffer2) {
  Lib_Print_print_compare(len, buffer1, buffer2);
  int res = 0;
  for (int i = 0; i < len; i++) {
    res |= buffer1[i] ^ buffer2[i];
  }
  if (res == 0) {
    printf("Success !\n");
  } else {
    printf("Failure !\n");
  }
  printf("\n");
}

