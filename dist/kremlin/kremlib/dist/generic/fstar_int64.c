/* Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
   Licensed under the Apache 2.0 License. */

#include "FStar_Int64.h"

Prims_string FStar_Int64_to_string(int64_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  KRML_HOST_SNPRINTF(buf, 24, "%"PRId64, i);
  return buf;
}

krml_checked_int_t FStar_Int64_v(int64_t x) {
  return x;
}
