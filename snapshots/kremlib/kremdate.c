#include "kremlib.h"
#include "kremlin/prims_int.h"

/******************************************************************************/
/* Implementation of FStar.Date                                               */
/******************************************************************************/

/* FStar_Date.h has all the extern val's. This is just the implementation. */

Prims_nat FStar_Date_secondsFromDawn() {
  return KRML_HOST_TIME();
}
