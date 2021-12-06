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


#include "Hacl_Hash_SHA1.h"

static u32
_h0[5U] =
  { (u32)0x67452301U, (u32)0xefcdab89U, (u32)0x98badcfeU, (u32)0x10325476U, (u32)0xc3d2e1f0U };

void Hacl_Hash_Core_SHA1_legacy_init(u32 *s)
{
  u32 i;
  for (i = (u32)0U; i < (u32)5U; i++)
    s[i] = _h0[i];
}

static void legacy_update(u32 *h, u8 *l)
{
  u32 ha = h[0U];
  u32 hb = h[1U];
  u32 hc = h[2U];
  u32 hd = h[3U];
  u32 he = h[4U];
  u32 _w[80U] = { 0U };
  u32 sta;
  u32 stb;
  u32 stc;
  u32 std;
  u32 ste;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)80U; i++)
    {
      u32 v;
      if (i < (u32)16U)
      {
        u8 *b = l + i * (u32)4U;
        u32 u = load32_be(b);
        v = u;
      }
      else
      {
        u32 wmit3 = _w[i - (u32)3U];
        u32 wmit8 = _w[i - (u32)8U];
        u32 wmit14 = _w[i - (u32)14U];
        u32 wmit16 = _w[i - (u32)16U];
        v =
          (wmit3 ^ (wmit8 ^ (wmit14 ^ wmit16)))
          << (u32)1U
          | (wmit3 ^ (wmit8 ^ (wmit14 ^ wmit16))) >> (u32)31U;
      }
      _w[i] = v;
    }
  }
  {
    u32 i;
    for (i = (u32)0U; i < (u32)80U; i++)
    {
      u32 _a = h[0U];
      u32 _b = h[1U];
      u32 _c = h[2U];
      u32 _d = h[3U];
      u32 _e = h[4U];
      u32 wmit = _w[i];
      u32 ite0;
      if (i < (u32)20U)
        ite0 = (_b & _c) ^ (~_b & _d);
      else if ((u32)39U < i && i < (u32)60U)
        ite0 = (_b & _c) ^ ((_b & _d) ^ (_c & _d));
      else
        ite0 = _b ^ (_c ^ _d);
      {
        u32 ite;
        if (i < (u32)20U)
          ite = (u32)0x5a827999U;
        else if (i < (u32)40U)
          ite = (u32)0x6ed9eba1U;
        else if (i < (u32)60U)
          ite = (u32)0x8f1bbcdcU;
        else
          ite = (u32)0xca62c1d6U;
        {
          u32 _T = (_a << (u32)5U | _a >> (u32)27U) + ite0 + _e + ite + wmit;
          h[0U] = _T;
          h[1U] = _a;
          h[2U] = _b << (u32)30U | _b >> (u32)2U;
          h[3U] = _c;
          h[4U] = _d;
        }
      }
    }
  }
  {
    u32 i;
    for (i = (u32)0U; i < (u32)80U; i++)
      _w[i] = (u32)0U;
  }
  sta = h[0U];
  stb = h[1U];
  stc = h[2U];
  std = h[3U];
  ste = h[4U];
  h[0U] = sta + ha;
  h[1U] = stb + hb;
  h[2U] = stc + hc;
  h[3U] = std + hd;
  h[4U] = ste + he;
}

static void legacy_pad(u64 len, u8 *dst)
{
  u8 *dst1 = dst;
  u8 *dst2;
  u8 *dst3;
  dst1[0U] = (u8)0x80U;
  dst2 = dst + (u32)1U;
  {
    u32 i;
    for (i = (u32)0U; i < ((u32)128U - ((u32)9U + (u32)(len % (u64)(u32)64U))) % (u32)64U; i++)
      dst2[i] = (u8)0U;
  }
  dst3 = dst + (u32)1U + ((u32)128U - ((u32)9U + (u32)(len % (u64)(u32)64U))) % (u32)64U;
  store64_be(dst3, len << (u32)3U);
}

void Hacl_Hash_Core_SHA1_legacy_finish(u32 *s, u8 *dst)
{
  u32 *uu____0 = s;
  u32 i;
  for (i = (u32)0U; i < (u32)5U; i++)
    store32_be(dst + i * (u32)4U, uu____0[i]);
}

void Hacl_Hash_SHA1_legacy_update_multi(u32 *s, u8 *blocks, u32 n_blocks)
{
  u32 i;
  for (i = (u32)0U; i < n_blocks; i++)
  {
    u32 sz = (u32)64U;
    u8 *block = blocks + sz * i;
    legacy_update(s, block);
  }
}

void Hacl_Hash_SHA1_legacy_update_last(u32 *s, u64 prev_len, u8 *input, u32 input_len)
{
  u32 blocks_n = input_len / (u32)64U;
  u32 blocks_len = blocks_n * (u32)64U;
  u8 *blocks = input;
  u32 rest_len = input_len - blocks_len;
  u8 *rest = input + blocks_len;
  u64 total_input_len;
  u32 pad_len;
  u32 tmp_len;
  Hacl_Hash_SHA1_legacy_update_multi(s, blocks, blocks_n);
  total_input_len = prev_len + (u64)input_len;
  pad_len =
    (u32)1U
    + ((u32)128U - ((u32)9U + (u32)(total_input_len % (u64)(u32)64U))) % (u32)64U
    + (u32)8U;
  tmp_len = rest_len + pad_len;
  {
    u8 tmp_twoblocks[128U] = { 0U };
    u8 *tmp = tmp_twoblocks;
    u8 *tmp_rest = tmp;
    u8 *tmp_pad = tmp + rest_len;
    memcpy(tmp_rest, rest, rest_len * sizeof (u8));
    legacy_pad(total_input_len, tmp_pad);
    Hacl_Hash_SHA1_legacy_update_multi(s, tmp, tmp_len / (u32)64U);
  }
}

void Hacl_Hash_SHA1_legacy_hash(u8 *input, u32 input_len, u8 *dst)
{
  u32
  scrut[5U] =
    { (u32)0x67452301U, (u32)0xefcdab89U, (u32)0x98badcfeU, (u32)0x10325476U, (u32)0xc3d2e1f0U };
  u32 *s = scrut;
  u32 blocks_n0 = input_len / (u32)64U;
  u32 blocks_n1;
  if (input_len % (u32)64U == (u32)0U && blocks_n0 > (u32)0U)
    blocks_n1 = blocks_n0 - (u32)1U;
  else
    blocks_n1 = blocks_n0;
  {
    u32 blocks_len0 = blocks_n1 * (u32)64U;
    u8 *blocks0 = input;
    u32 rest_len0 = input_len - blocks_len0;
    u8 *rest0 = input + blocks_len0;
    u32 blocks_n = blocks_n1;
    u32 blocks_len = blocks_len0;
    u8 *blocks = blocks0;
    u32 rest_len = rest_len0;
    u8 *rest = rest0;
    Hacl_Hash_SHA1_legacy_update_multi(s, blocks, blocks_n);
    Hacl_Hash_SHA1_legacy_update_last(s, (u64)blocks_len, rest, rest_len);
    Hacl_Hash_Core_SHA1_legacy_finish(s, dst);
  }
}

