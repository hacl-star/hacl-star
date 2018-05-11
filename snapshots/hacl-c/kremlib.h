/* MIT License
 *
 * Copyright (c) 2016-2017 INRIA and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
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
