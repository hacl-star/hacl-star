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


#include "internal/Hacl_Hash_SHA1.h"



static uint32_t
_h0[5U] =
  {
    (uint32_t)0x67452301U, (uint32_t)0xefcdab89U, (uint32_t)0x98badcfeU, (uint32_t)0x10325476U,
    (uint32_t)0xc3d2e1f0U
  };

void Hacl_Hash_Core_SHA1_legacy_init(uint32_t *s)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)5U; i++)
  {
    s[i] = _h0[i];
  }
}

void Hacl_Hash_Core_SHA1_legacy_update(uint32_t *h, uint8_t *l)
{
  uint32_t ha = h[0U];
  uint32_t hb = h[1U];
  uint32_t hc = h[2U];
  uint32_t hd = h[3U];
  uint32_t he = h[4U];
  uint32_t _w[80U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)80U; i++)
  {
    uint32_t v;
    if (i < (uint32_t)16U)
    {
      uint8_t *b = l + i * (uint32_t)4U;
      uint32_t u = load32_be(b);
      v = u;
    }
    else
    {
      uint32_t wmit3 = _w[i - (uint32_t)3U];
      uint32_t wmit8 = _w[i - (uint32_t)8U];
      uint32_t wmit14 = _w[i - (uint32_t)14U];
      uint32_t wmit16 = _w[i - (uint32_t)16U];
      v =
        (wmit3 ^ (wmit8 ^ (wmit14 ^ wmit16)))
        << (uint32_t)1U
        | (wmit3 ^ (wmit8 ^ (wmit14 ^ wmit16))) >> (uint32_t)31U;
    }
    _w[i] = v;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)80U; i++)
  {
    uint32_t _a = h[0U];
    uint32_t _b = h[1U];
    uint32_t _c = h[2U];
    uint32_t _d = h[3U];
    uint32_t _e = h[4U];
    uint32_t wmit = _w[i];
    uint32_t ite0;
    if (i < (uint32_t)20U)
    {
      ite0 = (_b & _c) ^ (~_b & _d);
    }
    else if ((uint32_t)39U < i && i < (uint32_t)60U)
    {
      ite0 = (_b & _c) ^ ((_b & _d) ^ (_c & _d));
    }
    else
    {
      ite0 = _b ^ (_c ^ _d);
    }
    uint32_t ite;
    if (i < (uint32_t)20U)
    {
      ite = (uint32_t)0x5a827999U;
    }
    else if (i < (uint32_t)40U)
    {
      ite = (uint32_t)0x6ed9eba1U;
    }
    else if (i < (uint32_t)60U)
    {
      ite = (uint32_t)0x8f1bbcdcU;
    }
    else
    {
      ite = (uint32_t)0xca62c1d6U;
    }
    uint32_t _T = (_a << (uint32_t)5U | _a >> (uint32_t)27U) + ite0 + _e + ite + wmit;
    h[0U] = _T;
    h[1U] = _a;
    h[2U] = _b << (uint32_t)30U | _b >> (uint32_t)2U;
    h[3U] = _c;
    h[4U] = _d;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)80U; i++)
  {
    _w[i] = (uint32_t)0U;
  }
  uint32_t sta = h[0U];
  uint32_t stb = h[1U];
  uint32_t stc = h[2U];
  uint32_t std = h[3U];
  uint32_t ste = h[4U];
  h[0U] = sta + ha;
  h[1U] = stb + hb;
  h[2U] = stc + hc;
  h[3U] = std + hd;
  h[4U] = ste + he;
}

static void legacy_pad(uint64_t len, uint8_t *dst)
{
  uint8_t *dst1 = dst;
  dst1[0U] = (uint8_t)0x80U;
  uint8_t *dst2 = dst + (uint32_t)1U;
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    < ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(len % (uint64_t)(uint32_t)64U))) % (uint32_t)64U;
    i++)
  {
    dst2[i] = (uint8_t)0U;
  }
  uint8_t
  *dst3 =
    dst
    +
      (uint32_t)1U
      +
        ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(len % (uint64_t)(uint32_t)64U)))
        % (uint32_t)64U;
  store64_be(dst3, len << (uint32_t)3U);
}

void Hacl_Hash_Core_SHA1_legacy_finish(uint32_t *s, uint8_t *dst)
{
  uint32_t *uu____0 = s;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)5U; i++)
  {
    store32_be(dst + i * (uint32_t)4U, uu____0[i]);
  }
}

void Hacl_Hash_SHA1_legacy_update_multi(uint32_t *s, uint8_t *blocks, uint32_t n_blocks)
{
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i++)
  {
    uint32_t sz = (uint32_t)64U;
    uint8_t *block = blocks + sz * i;
    Hacl_Hash_Core_SHA1_legacy_update(s, block);
  }
}

void
Hacl_Hash_SHA1_legacy_update_last(
  uint32_t *s,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
)
{
  uint32_t blocks_n = input_len / (uint32_t)64U;
  uint32_t blocks_len = blocks_n * (uint32_t)64U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  Hacl_Hash_SHA1_legacy_update_multi(s, blocks, blocks_n);
  uint64_t total_input_len = prev_len + (uint64_t)input_len;
  uint32_t
  pad_len =
    (uint32_t)1U
    +
      ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(total_input_len % (uint64_t)(uint32_t)64U)))
      % (uint32_t)64U
    + (uint32_t)8U;
  uint32_t tmp_len = rest_len + pad_len;
  uint8_t tmp_twoblocks[128U] = { 0U };
  uint8_t *tmp = tmp_twoblocks;
  uint8_t *tmp_rest = tmp;
  uint8_t *tmp_pad = tmp + rest_len;
  memcpy(tmp_rest, rest, rest_len * sizeof (uint8_t));
  legacy_pad(total_input_len, tmp_pad);
  Hacl_Hash_SHA1_legacy_update_multi(s, tmp, tmp_len / (uint32_t)64U);
}

void Hacl_Hash_SHA1_legacy_hash(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint32_t
  scrut[5U] =
    {
      (uint32_t)0x67452301U, (uint32_t)0xefcdab89U, (uint32_t)0x98badcfeU, (uint32_t)0x10325476U,
      (uint32_t)0xc3d2e1f0U
    };
  uint32_t *s = scrut;
  uint32_t blocks_n0 = input_len / (uint32_t)64U;
  uint32_t blocks_n1;
  if (input_len % (uint32_t)64U == (uint32_t)0U && blocks_n0 > (uint32_t)0U)
  {
    blocks_n1 = blocks_n0 - (uint32_t)1U;
  }
  else
  {
    blocks_n1 = blocks_n0;
  }
  uint32_t blocks_len0 = blocks_n1 * (uint32_t)64U;
  uint8_t *blocks0 = input;
  uint32_t rest_len0 = input_len - blocks_len0;
  uint8_t *rest0 = input + blocks_len0;
  uint32_t blocks_n = blocks_n1;
  uint32_t blocks_len = blocks_len0;
  uint8_t *blocks = blocks0;
  uint32_t rest_len = rest_len0;
  uint8_t *rest = rest0;
  Hacl_Hash_SHA1_legacy_update_multi(s, blocks, blocks_n);
  Hacl_Hash_SHA1_legacy_update_last(s, (uint64_t)blocks_len, rest, rest_len);
  Hacl_Hash_Core_SHA1_legacy_finish(s, dst);
}

