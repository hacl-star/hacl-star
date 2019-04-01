/* Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
   Licensed under the Apache 2.0 License. */

#include "FStar_UInt_8_16_32_64.h"

Prims_string FStar_UInt64_to_string(uint64_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  KRML_HOST_SNPRINTF(buf, 24, "%"PRIu64, i);
  return buf;
}

uint64_t FStar_UInt64_uint_to_t(krml_checked_int_t x) {
  /* TODO bounds check */
  return x;
}

krml_checked_int_t FStar_UInt64_v(uint64_t x) {
  RETURN_OR(x);
}
