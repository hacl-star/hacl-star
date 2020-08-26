/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
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


#ifndef __Hacl_Impl_Blake2_Constants_H
#define __Hacl_Impl_Blake2_Constants_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"




static const
u32
Hacl_Impl_Blake2_Constants_sigmaTable[160U] =
  {
    (u32)0U, (u32)1U, (u32)2U, (u32)3U, (u32)4U, (u32)5U, (u32)6U, (u32)7U, (u32)8U, (u32)9U,
    (u32)10U, (u32)11U, (u32)12U, (u32)13U, (u32)14U, (u32)15U, (u32)14U, (u32)10U, (u32)4U,
    (u32)8U, (u32)9U, (u32)15U, (u32)13U, (u32)6U, (u32)1U, (u32)12U, (u32)0U, (u32)2U, (u32)11U,
    (u32)7U, (u32)5U, (u32)3U, (u32)11U, (u32)8U, (u32)12U, (u32)0U, (u32)5U, (u32)2U, (u32)15U,
    (u32)13U, (u32)10U, (u32)14U, (u32)3U, (u32)6U, (u32)7U, (u32)1U, (u32)9U, (u32)4U, (u32)7U,
    (u32)9U, (u32)3U, (u32)1U, (u32)13U, (u32)12U, (u32)11U, (u32)14U, (u32)2U, (u32)6U, (u32)5U,
    (u32)10U, (u32)4U, (u32)0U, (u32)15U, (u32)8U, (u32)9U, (u32)0U, (u32)5U, (u32)7U, (u32)2U,
    (u32)4U, (u32)10U, (u32)15U, (u32)14U, (u32)1U, (u32)11U, (u32)12U, (u32)6U, (u32)8U, (u32)3U,
    (u32)13U, (u32)2U, (u32)12U, (u32)6U, (u32)10U, (u32)0U, (u32)11U, (u32)8U, (u32)3U, (u32)4U,
    (u32)13U, (u32)7U, (u32)5U, (u32)15U, (u32)14U, (u32)1U, (u32)9U, (u32)12U, (u32)5U, (u32)1U,
    (u32)15U, (u32)14U, (u32)13U, (u32)4U, (u32)10U, (u32)0U, (u32)7U, (u32)6U, (u32)3U, (u32)9U,
    (u32)2U, (u32)8U, (u32)11U, (u32)13U, (u32)11U, (u32)7U, (u32)14U, (u32)12U, (u32)1U, (u32)3U,
    (u32)9U, (u32)5U, (u32)0U, (u32)15U, (u32)4U, (u32)8U, (u32)6U, (u32)2U, (u32)10U, (u32)6U,
    (u32)15U, (u32)14U, (u32)9U, (u32)11U, (u32)3U, (u32)0U, (u32)8U, (u32)12U, (u32)2U, (u32)13U,
    (u32)7U, (u32)1U, (u32)4U, (u32)10U, (u32)5U, (u32)10U, (u32)2U, (u32)8U, (u32)4U, (u32)7U,
    (u32)6U, (u32)1U, (u32)5U, (u32)15U, (u32)11U, (u32)9U, (u32)14U, (u32)3U, (u32)12U, (u32)13U
  };

static const
u32
Hacl_Impl_Blake2_Constants_ivTable_S[8U] =
  {
    (u32)0x6A09E667U, (u32)0xBB67AE85U, (u32)0x3C6EF372U, (u32)0xA54FF53AU, (u32)0x510E527FU,
    (u32)0x9B05688CU, (u32)0x1F83D9ABU, (u32)0x5BE0CD19U
  };

static const
u64
Hacl_Impl_Blake2_Constants_ivTable_B[8U] =
  {
    (u64)0x6A09E667F3BCC908U, (u64)0xBB67AE8584CAA73BU, (u64)0x3C6EF372FE94F82BU,
    (u64)0xA54FF53A5F1D36F1U, (u64)0x510E527FADE682D1U, (u64)0x9B05688C2B3E6C1FU,
    (u64)0x1F83D9ABFB41BD6BU, (u64)0x5BE0CD19137E2179U
  };

#if defined(__cplusplus)
}
#endif

#define __Hacl_Impl_Blake2_Constants_H_DEFINED
#endif
