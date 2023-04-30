/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
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


#ifndef __internal_Hacl_P256_H
#define __internal_Hacl_P256_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "internal/Hacl_P256_PrecompTable.h"
#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_Bignum_Base.h"
#include "../Hacl_P256.h"
#include "lib_intrinsics.h"

/* SNIPPET_START: Hacl_Impl_P256_DH_ecp256dh_i */

bool Hacl_Impl_P256_DH_ecp256dh_i(uint8_t *public_key, uint8_t *private_key);

/* SNIPPET_END: Hacl_Impl_P256_DH_ecp256dh_i */

/* SNIPPET_START: Hacl_Impl_P256_DH_ecp256dh_r */

bool
Hacl_Impl_P256_DH_ecp256dh_r(
  uint8_t *shared_secret,
  uint8_t *their_pubkey,
  uint8_t *private_key
);

/* SNIPPET_END: Hacl_Impl_P256_DH_ecp256dh_r */

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_P256_H_DEFINED
#endif
