#include "kremlib.h"
#include <stdlib.h>

int exit_success = EXIT_SUCCESS;
int exit_failure = EXIT_FAILURE;

void print_string(const char *s) {
  printf("%s", s);
}

void print_bytes(uint8_t *b, uint32_t len) {
  uint32_t i;
  for (i = 0; i < len; i++){
    printf("%02x", b[i]);
  }
  printf("\n");
}
