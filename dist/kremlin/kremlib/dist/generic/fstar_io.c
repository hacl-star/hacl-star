/* Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
   Licensed under the Apache 2.0 License. */

#include "FStar_IO.h"

bool FStar_IO_debug_print_string(Prims_string s) {
  KRML_HOST_PRINTF("%s", s);
  return false;
}
