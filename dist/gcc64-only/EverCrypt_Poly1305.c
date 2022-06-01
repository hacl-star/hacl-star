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


#include "EverCrypt_Poly1305.h"

#include "internal/Vale.h"

static void poly1305_vale(uint8_t *dst, uint8_t *src, uint32_t len, uint8_t *key)
{
  uint8_t ctx[192U] = { 0U };
  memcpy(ctx + (uint32_t)24U, key, (uint32_t)32U * sizeof (uint8_t));
  uint32_t n_blocks = len / (uint32_t)16U;
  uint32_t n_extra = len % (uint32_t)16U;
  uint8_t tmp[16U];
  if (n_extra == (uint32_t)0U)
  {
    uint64_t scrut = x64_poly1305(ctx, src, (uint64_t)len, (uint64_t)1U);
  }
  else
  {
    uint8_t init = (uint8_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      tmp[i] = init;
    }
    uint32_t len16 = n_blocks * (uint32_t)16U;
    uint8_t *src16 = src;
    memcpy(tmp, src + len16, n_extra * sizeof (uint8_t));
    uint64_t scrut = x64_poly1305(ctx, src16, (uint64_t)len16, (uint64_t)0U);
    memcpy(ctx + (uint32_t)24U, key, (uint32_t)32U * sizeof (uint8_t));
    uint64_t scrut0 = x64_poly1305(ctx, tmp, (uint64_t)n_extra, (uint64_t)1U);
  }
  memcpy(dst, ctx, (uint32_t)16U * sizeof (uint8_t));
}

void EverCrypt_Poly1305_poly1305(uint8_t *dst, uint8_t *src, uint32_t len, uint8_t *key)
{
  bool avx2 = EverCrypt_AutoConfig2_has_avx2();
  bool avx = EverCrypt_AutoConfig2_has_avx();
  bool vec256 = EverCrypt_AutoConfig2_has_vec256();
  bool vec128 = EverCrypt_AutoConfig2_has_vec128();
  bool vale = EverCrypt_AutoConfig2_wants_vale();
  #if HACL_CAN_COMPILE_VEC256
  if (vec256)
  {
    Hacl_Poly1305_256_poly1305_mac(dst, len, src, key);
    return;
  }
  #endif
  #if HACL_CAN_COMPILE_VEC128
  if (vec128)
  {
    Hacl_Poly1305_128_poly1305_mac(dst, len, src, key);
    return;
  }
  #endif
  #if HACL_CAN_COMPILE_VALE
  if (vale)
  {
    poly1305_vale(dst, src, len, key);
    return;
  }
  #endif
  Hacl_Poly1305_32_poly1305_mac(dst, len, src, key);
}

