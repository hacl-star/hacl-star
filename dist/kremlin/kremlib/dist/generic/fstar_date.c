/* Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
   Licensed under the Apache 2.0 License. */

#include "FStar_Date.h"

/******************************************************************************/
/* Implementation of FStar.Date                                               */
/******************************************************************************/

Prims_nat FStar_Date_secondsFromDawn() {
  return KRML_HOST_TIME();
}
