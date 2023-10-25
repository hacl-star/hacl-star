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


#include "EverCrypt_Poly1305.h"

#include "internal/Vale.h"
#include "config.h"

KRML_MAYBE_UNUSED static void
poly1305_vale(uint8_t *dst, uint8_t *src, uint32_t len, uint8_t *key)
{
  KRML_MAYBE_UNUSED_VAR(dst);
  KRML_MAYBE_UNUSED_VAR(src);
  KRML_MAYBE_UNUSED_VAR(len);
  KRML_MAYBE_UNUSED_VAR(key);
  #if HACL_CAN_COMPILE_VALE
  uint8_t ctx[192U] = { 0U };
  memcpy(ctx + 24U, key, 32U * sizeof (uint8_t));
  uint32_t n_blocks = len / 16U;
  uint32_t n_extra = len % 16U;
  uint8_t tmp[16U] = { 0U };
  if (n_extra == 0U)
  {
    x64_poly1305(ctx, src, (uint64_t)len, 1ULL);
  }
  else
  {
    uint32_t len16 = n_blocks * 16U;
    uint8_t *src16 = src;
    memcpy(tmp, src + len16, n_extra * sizeof (uint8_t));
    x64_poly1305(ctx, src16, (uint64_t)len16, 0ULL);
    memcpy(ctx + 24U, key, 32U * sizeof (uint8_t));
    x64_poly1305(ctx, tmp, (uint64_t)n_extra, 1ULL);
  }
  memcpy(dst, ctx, 16U * sizeof (uint8_t));
  #endif
}

void EverCrypt_Poly1305_mac(uint8_t *output, uint8_t *input, uint32_t input_len, uint8_t *key)
{
  bool vec256 = EverCrypt_AutoConfig2_has_vec256();
  bool vec128 = EverCrypt_AutoConfig2_has_vec128();
  #if HACL_CAN_COMPILE_VEC256
  if (vec256)
  {
    KRML_MAYBE_UNUSED_VAR(vec128);
    Hacl_MAC_Poly1305_Simd256_mac(output, input, input_len, key);
    return;
  }
  #endif
  #if HACL_CAN_COMPILE_VEC128
  if (vec128)
  {
    KRML_MAYBE_UNUSED_VAR(vec256);
    Hacl_MAC_Poly1305_Simd128_mac(output, input, input_len, key);
    return;
  }
  #endif
  KRML_MAYBE_UNUSED_VAR(vec256);
  KRML_MAYBE_UNUSED_VAR(vec128);
  #if HACL_CAN_COMPILE_VALE
  poly1305_vale(output, input, input_len, key);
  #else
  KRML_HOST_IGNORE(poly1305_vale);
  Hacl_MAC_Poly1305_mac(output, input, input_len, key);
  #endif
}

