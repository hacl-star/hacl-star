/* Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
   Licensed under the Apache 2.0 License. */

#include "C_String.h"

C_String_t C_String_of_literal(const char *str) {
  return str;
}

void C_String_print(C_String_t str) {
  KRML_HOST_PRINTF("%s", str);
}

uint32_t C_String_strlen(C_String_t x0) {
  size_t s = strlen(x0);
  if (s > UINT32_MAX) {
    KRML_HOST_EPRINTF("Overflow in C_String_strlen");
    KRML_HOST_EXIT(255);
  }
  return s;
}

void C_String_memcpy(uint8_t *dst, C_String_t src, uint32_t len) {
  memcpy((char*)dst, src, len);
}
