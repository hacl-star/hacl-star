/* Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
   Licensed under the Apache 2.0 License. */

#include "FStar_UInt_8_16_32_64.h"

Prims_string FStar_UInt16_to_string(uint16_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  KRML_HOST_SNPRINTF(buf, 24, "%"PRIu16, i);
  return buf;
}

uint16_t FStar_UInt16_uint_to_t(krml_checked_int_t x) {
  /* TODO bounds check */
  return x;
}

krml_checked_int_t FStar_UInt16_v(uint16_t x) {
  return x;
}
