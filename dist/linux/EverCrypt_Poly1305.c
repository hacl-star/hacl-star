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

static void EverCrypt_Poly1305_poly1305_vale(u8 *dst, u8 *src, u32 len, u8 *key)
{
  u8 ctx[192U] = { 0U };
  u32 n_blocks;
  u32 n_extra;
  memcpy(ctx + (u32)24U, key, (u32)32U * sizeof key[0U]);
  n_blocks = len / (u32)16U;
  n_extra = len % (u32)16U;
  {
    u8 tmp[16U];
    if (n_extra == (u32)0U)
    {
      u64 scrut = x64_poly1305(ctx, src, (u64)len, (u64)1U);
    }
    else
    {
      u8 init = (u8)0U;
      {
        u32 i;
        for (i = (u32)0U; i < (u32)16U; i = i + (u32)1U)
        {
          tmp[i] = init;
        }
      }
      {
        u32 len16 = n_blocks * (u32)16U;
        u8 *src16 = src;
        memcpy(tmp, src + len16, n_extra * sizeof src[0U]);
        {
          u64 scrut = x64_poly1305(ctx, src16, (u64)len16, (u64)0U);
          memcpy(ctx + (u32)24U, key, (u32)32U * sizeof key[0U]);
          {
            u64 scrut0 = x64_poly1305(ctx, tmp, (u64)n_extra, (u64)1U);
          }
        }
      }
    }
    memcpy(dst, ctx, (u32)16U * sizeof ctx[0U]);
  }
}

void EverCrypt_Poly1305_poly1305(u8 *dst, u8 *src, u32 len, u8 *key)
{
  bool avx2 = EverCrypt_AutoConfig2_has_avx2();
  bool avx = EverCrypt_AutoConfig2_has_avx();
  bool vale = EverCrypt_AutoConfig2_wants_vale();
  #if EVERCRYPT_TARGETCONFIG_X64
  if (avx2)
  {
    Hacl_Poly1305_256_poly1305_mac(dst, len, src, key);
    return;
  }
  #endif
  #if EVERCRYPT_TARGETCONFIG_X64
  if (avx)
  {
    Hacl_Poly1305_128_poly1305_mac(dst, len, src, key);
    return;
  }
  #endif
  #if EVERCRYPT_TARGETCONFIG_X64
  if (vale)
  {
    EverCrypt_Poly1305_poly1305_vale(dst, src, len, key);
    return;
  }
  #endif
  Hacl_Poly1305_32_poly1305_mac(dst, len, src, key);
}

