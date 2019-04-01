/* Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
   Licensed under the Apache 2.0 License. */

#include "FStar_Int16.h"

Prims_string FStar_Int16_to_string(int16_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  KRML_HOST_SNPRINTF(buf, 24, "%"PRId16, i);
  return buf;
}
