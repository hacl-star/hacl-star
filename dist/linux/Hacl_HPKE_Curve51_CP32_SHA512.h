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


#ifndef __Hacl_HPKE_Curve51_CP32_SHA512_H
#define __Hacl_HPKE_Curve51_CP32_SHA512_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Hacl_Spec.h"
#include "Hacl_Krmllib.h"
#include "Hacl_Impl_HPKE.h"
#include "Hacl_HKDF.h"
#include "Hacl_Curve25519_51.h"
#include "Hacl_Chacha20Poly1305_32.h"
#include "libintvector.h"
u32
Hacl_HPKE_Curve51_CP32_SHA512_setupBaseS(
  u8 *o_pkE,
  Hacl_Impl_HPKE_context_s o_ctx,
  u8 *skE,
  u8 *pkR,
  u32 infolen,
  u8 *info
);

u32
Hacl_HPKE_Curve51_CP32_SHA512_setupBaseR(
  Hacl_Impl_HPKE_context_s o_ctx,
  u8 *enc,
  u8 *skR,
  u32 infolen,
  u8 *info
);

u32
Hacl_HPKE_Curve51_CP32_SHA512_sealBase(
  u8 *skE,
  u8 *pkR,
  u32 infolen,
  u8 *info,
  u32 aadlen,
  u8 *aad,
  u32 plainlen,
  u8 *plain,
  u8 *o_enc,
  u8 *o_ct
);

u32
Hacl_HPKE_Curve51_CP32_SHA512_openBase(
  u8 *pkE,
  u8 *skR,
  u32 infolen,
  u8 *info,
  u32 aadlen,
  u8 *aad,
  u32 ctlen,
  u8 *ct,
  u8 *o_pt
);

#if defined(__cplusplus)
}
#endif

#define __Hacl_HPKE_Curve51_CP32_SHA512_H_DEFINED
#endif
