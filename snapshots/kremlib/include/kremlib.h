#ifndef __KREMLIB_H
#define __KREMLIB_H

/******************************************************************************/
/* The all-in-one kremlib.h header                                            */
/******************************************************************************/

/* This is a meta-header that is included by default in KreMLin generated
 * programs. If you wish to have a more lightweight set of headers, or are
 * targeting an environment where controlling these macros yourself is
 * important, consider using:
 *
 *   krml -minimal
 *
 * to disable the inclusion of this file (note: this also disables the default
 * argument "-bundle FStar.*"). You can then include the headers of your choice
 * one by one, using -add-early-include. */

#include "kremlin/internal/target.h"
#include "kremlin/internal/callconv.h"
#include "kremlin/internal/builtin.h"
#include "kremlin/internal/debug.h"

typedef struct {
  uint32_t length;
  const char *data;
} FStar_Bytes_bytes;

#include "kremlin/c.h"
#include "kremlin/c_endianness.h"
#include "kremlin/fstar_dyn.h"
#include "kremlin/fstar_ints.h"
#include "kremlin/fstar_uint128.h"

#endif     /* __KREMLIB_H */
