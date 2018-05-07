#ifdef KRML_NOUINT128

#include "FStar_UInt128.h"
#include "kremlib.h"
/* Because of FStar_UInt128_v */
#include "kremlin/prims_int.h"

#define FStar_UInt64_add_underspec(X, Y) ((X) + (Y))
#define FStar_UInt64_sub_underspec(X, Y) ((X) - (Y))

#include "FStar_UInt128.c"

#endif
