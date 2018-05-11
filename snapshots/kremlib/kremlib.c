#include "kremlib.h"
#include <stdlib.h>

intptr_t nullptr = (intptr_t) NULL;

/* DEPRECATED */
int exit_success = EXIT_SUCCESS;
int exit_failure = EXIT_FAILURE;

void print_bytes(const uint8_t *b, uint32_t len) {
  uint32_t i;
  for (i = 0; i < len; i++){
    printf("%02x", b[i]);
  }
  printf("\n");
}
