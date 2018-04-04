#ifdef KRML_NOUINT128

#include "FStar_UInt128.h"
#include "kremlib.h"

#define FStar_UInt64_add_underspec(X, Y) ((X) + (Y))
#define FStar_UInt64_sub_underspec(X, Y) ((X) - (Y))

#include "FStar_UInt128.c"

#endif
