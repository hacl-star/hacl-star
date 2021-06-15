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

#include "target.h"
#include "callconv.h"
#include "builtin.h"
#include "debug.h"
#include "types.h"

#include "kremlin/lowstar_endianness.h"
#include "fstar_int.h"

#endif     /* __KREMLIB_H */
