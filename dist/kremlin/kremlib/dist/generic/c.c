/* Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
   Licensed under the Apache 2.0 License. */

#include <stdlib.h>
#include <stdbool.h>

#include "C.h"

intptr_t nullptr = (intptr_t) NULL;

bool __eq__C_char(char c1, char c2) {
  return c1 == c2;
}

void print_bytes(uint8_t *b, uint32_t len) {
  uint32_t i;
  for (i = 0; i < len; i++){
    KRML_HOST_PRINTF("%02x", b[i]);
  }
  KRML_HOST_PRINTF("\n");
}

void portable_exit(int code) {
  KRML_HOST_EXIT(code);
}
