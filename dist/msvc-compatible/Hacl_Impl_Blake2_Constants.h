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

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"




static const
uint32_t
Hacl_Impl_Blake2_Constants_sigmaTable[160U] =
  {
    (uint32_t)0U, (uint32_t)1U, (uint32_t)2U, (uint32_t)3U, (uint32_t)4U, (uint32_t)5U,
    (uint32_t)6U, (uint32_t)7U, (uint32_t)8U, (uint32_t)9U, (uint32_t)10U, (uint32_t)11U,
    (uint32_t)12U, (uint32_t)13U, (uint32_t)14U, (uint32_t)15U, (uint32_t)14U, (uint32_t)10U,
    (uint32_t)4U, (uint32_t)8U, (uint32_t)9U, (uint32_t)15U, (uint32_t)13U, (uint32_t)6U,
    (uint32_t)1U, (uint32_t)12U, (uint32_t)0U, (uint32_t)2U, (uint32_t)11U, (uint32_t)7U,
    (uint32_t)5U, (uint32_t)3U, (uint32_t)11U, (uint32_t)8U, (uint32_t)12U, (uint32_t)0U,
    (uint32_t)5U, (uint32_t)2U, (uint32_t)15U, (uint32_t)13U, (uint32_t)10U, (uint32_t)14U,
    (uint32_t)3U, (uint32_t)6U, (uint32_t)7U, (uint32_t)1U, (uint32_t)9U, (uint32_t)4U,
    (uint32_t)7U, (uint32_t)9U, (uint32_t)3U, (uint32_t)1U, (uint32_t)13U, (uint32_t)12U,
    (uint32_t)11U, (uint32_t)14U, (uint32_t)2U, (uint32_t)6U, (uint32_t)5U, (uint32_t)10U,
    (uint32_t)4U, (uint32_t)0U, (uint32_t)15U, (uint32_t)8U, (uint32_t)9U, (uint32_t)0U,
    (uint32_t)5U, (uint32_t)7U, (uint32_t)2U, (uint32_t)4U, (uint32_t)10U, (uint32_t)15U,
    (uint32_t)14U, (uint32_t)1U, (uint32_t)11U, (uint32_t)12U, (uint32_t)6U, (uint32_t)8U,
    (uint32_t)3U, (uint32_t)13U, (uint32_t)2U, (uint32_t)12U, (uint32_t)6U, (uint32_t)10U,
    (uint32_t)0U, (uint32_t)11U, (uint32_t)8U, (uint32_t)3U, (uint32_t)4U, (uint32_t)13U,
    (uint32_t)7U, (uint32_t)5U, (uint32_t)15U, (uint32_t)14U, (uint32_t)1U, (uint32_t)9U,
    (uint32_t)12U, (uint32_t)5U, (uint32_t)1U, (uint32_t)15U, (uint32_t)14U, (uint32_t)13U,
    (uint32_t)4U, (uint32_t)10U, (uint32_t)0U, (uint32_t)7U, (uint32_t)6U, (uint32_t)3U,
    (uint32_t)9U, (uint32_t)2U, (uint32_t)8U, (uint32_t)11U, (uint32_t)13U, (uint32_t)11U,
    (uint32_t)7U, (uint32_t)14U, (uint32_t)12U, (uint32_t)1U, (uint32_t)3U, (uint32_t)9U,
    (uint32_t)5U, (uint32_t)0U, (uint32_t)15U, (uint32_t)4U, (uint32_t)8U, (uint32_t)6U,
    (uint32_t)2U, (uint32_t)10U, (uint32_t)6U, (uint32_t)15U, (uint32_t)14U, (uint32_t)9U,
    (uint32_t)11U, (uint32_t)3U, (uint32_t)0U, (uint32_t)8U, (uint32_t)12U, (uint32_t)2U,
    (uint32_t)13U, (uint32_t)7U, (uint32_t)1U, (uint32_t)4U, (uint32_t)10U, (uint32_t)5U,
    (uint32_t)10U, (uint32_t)2U, (uint32_t)8U, (uint32_t)4U, (uint32_t)7U, (uint32_t)6U,
    (uint32_t)1U, (uint32_t)5U, (uint32_t)15U, (uint32_t)11U, (uint32_t)9U, (uint32_t)14U,
    (uint32_t)3U, (uint32_t)12U, (uint32_t)13U
  };

static const
uint32_t
Hacl_Impl_Blake2_Constants_ivTable_S[8U] =
  {
    (uint32_t)0x6A09E667U, (uint32_t)0xBB67AE85U, (uint32_t)0x3C6EF372U, (uint32_t)0xA54FF53AU,
    (uint32_t)0x510E527FU, (uint32_t)0x9B05688CU, (uint32_t)0x1F83D9ABU, (uint32_t)0x5BE0CD19U
  };

static const
uint64_t
Hacl_Impl_Blake2_Constants_ivTable_B[8U] =
  {
    (uint64_t)0x6A09E667F3BCC908U, (uint64_t)0xBB67AE8584CAA73BU, (uint64_t)0x3C6EF372FE94F82BU,
    (uint64_t)0xA54FF53A5F1D36F1U, (uint64_t)0x510E527FADE682D1U, (uint64_t)0x9B05688C2B3E6C1FU,
    (uint64_t)0x1F83D9ABFB41BD6BU, (uint64_t)0x5BE0CD19137E2179U
  };

#if defined(__cplusplus)
}
#endif

#define __Hacl_Impl_Blake2_Constants_H_DEFINED
#endif
