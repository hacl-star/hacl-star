#include <string.h>
/* #include "kremlin/internal/target.h" */
/* #include "kremlin/internal/callconv.h" */
/* #include "kremlin/internal/builtin.h" */
/* #include "kremlin/internal/debug.h" */
/* #include "kremlin/internal/types.h" */

/* #include "kremlin/lowstar_endianness.h" */
/* #include "kremlin/fstar_int.h" */
#ifndef __C_Test_Blake2b_Incremental_H
#define __C_Test_Blake2b_Incremental_H

#include "C_String.h"
#include "Hacl_Blake2b.h"
#include "c/Lib_PrintBuffer.h"

bool
test_blake2b(uint32_t ll, uint8_t *d, uint32_t kk, uint8_t *k, uint32_t nn, uint8_t *expected);

exit_code main();

#define __C_Test_Blake2b_Incremental_H_DEFINED
#endif
