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


#include "Hacl_Test_HMAC_DRBG.h"

#define SHA2_224 0
#define SHA2_256 1
#define SHA2_384 2
#define SHA2_512 3
#define SHA1 4
#define MD5 5
#define Blake2S 6
#define Blake2B 7
#define SHA3_256 8
#define SHA3_224 9
#define SHA3_384 10
#define SHA3_512 11
#define Shake128 12
#define Shake256 13

typedef uint8_t hash_alg;

static inline void sha256_init(uint32_t *hash)
{
  for (uint32_t i = 0U; i < 8U; i++)
  {
    uint32_t *os = hash;
    uint32_t x = Hacl_Impl_SHA2_Generic_h256[i];
    os[i] = x;
  }
}

static inline void sha256_update(uint8_t *b, uint32_t *hash)
{
  uint32_t hash_old[8U] = { 0U };
  uint32_t ws[16U] = { 0U };
  memcpy(hash_old, hash, 8U * sizeof (uint32_t));
  uint8_t *b10 = b;
  uint32_t u = load32_be(b10);
  ws[0U] = u;
  uint32_t u0 = load32_be(b10 + 4U);
  ws[1U] = u0;
  uint32_t u1 = load32_be(b10 + 8U);
  ws[2U] = u1;
  uint32_t u2 = load32_be(b10 + 12U);
  ws[3U] = u2;
  uint32_t u3 = load32_be(b10 + 16U);
  ws[4U] = u3;
  uint32_t u4 = load32_be(b10 + 20U);
  ws[5U] = u4;
  uint32_t u5 = load32_be(b10 + 24U);
  ws[6U] = u5;
  uint32_t u6 = load32_be(b10 + 28U);
  ws[7U] = u6;
  uint32_t u7 = load32_be(b10 + 32U);
  ws[8U] = u7;
  uint32_t u8 = load32_be(b10 + 36U);
  ws[9U] = u8;
  uint32_t u9 = load32_be(b10 + 40U);
  ws[10U] = u9;
  uint32_t u10 = load32_be(b10 + 44U);
  ws[11U] = u10;
  uint32_t u11 = load32_be(b10 + 48U);
  ws[12U] = u11;
  uint32_t u12 = load32_be(b10 + 52U);
  ws[13U] = u12;
  uint32_t u13 = load32_be(b10 + 56U);
  ws[14U] = u13;
  uint32_t u14 = load32_be(b10 + 60U);
  ws[15U] = u14;
  for (uint32_t i0 = 0U; i0 < 4U; i0++)
  {
    for (uint32_t i = 0U; i < 16U; i++)
    {
      uint32_t k_t = Hacl_Impl_SHA2_Generic_k224_256[16U * i0 + i];
      uint32_t ws_t = ws[i];
      uint32_t a0 = hash[0U];
      uint32_t b0 = hash[1U];
      uint32_t c0 = hash[2U];
      uint32_t d0 = hash[3U];
      uint32_t e0 = hash[4U];
      uint32_t f0 = hash[5U];
      uint32_t g0 = hash[6U];
      uint32_t h02 = hash[7U];
      uint32_t k_e_t = k_t;
      uint32_t
      t1 =
        h02
        + ((e0 << 26U | e0 >> 6U) ^ ((e0 << 21U | e0 >> 11U) ^ (e0 << 7U | e0 >> 25U)))
        + ((e0 & f0) ^ (~e0 & g0))
        + k_e_t
        + ws_t;
      uint32_t
      t2 =
        ((a0 << 30U | a0 >> 2U) ^ ((a0 << 19U | a0 >> 13U) ^ (a0 << 10U | a0 >> 22U)))
        + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
      uint32_t a1 = t1 + t2;
      uint32_t b1 = a0;
      uint32_t c1 = b0;
      uint32_t d1 = c0;
      uint32_t e1 = d0 + t1;
      uint32_t f1 = e0;
      uint32_t g1 = f0;
      uint32_t h12 = g0;
      hash[0U] = a1;
      hash[1U] = b1;
      hash[2U] = c1;
      hash[3U] = d1;
      hash[4U] = e1;
      hash[5U] = f1;
      hash[6U] = g1;
      hash[7U] = h12;
    }
    if (i0 < 3U)
    {
      for (uint32_t i = 0U; i < 16U; i++)
      {
        uint32_t t16 = ws[i];
        uint32_t t15 = ws[(i + 1U) % 16U];
        uint32_t t7 = ws[(i + 9U) % 16U];
        uint32_t t2 = ws[(i + 14U) % 16U];
        uint32_t s1 = (t2 << 15U | t2 >> 17U) ^ ((t2 << 13U | t2 >> 19U) ^ t2 >> 10U);
        uint32_t s0 = (t15 << 25U | t15 >> 7U) ^ ((t15 << 14U | t15 >> 18U) ^ t15 >> 3U);
        ws[i] = s1 + t7 + s0 + t16;
      }
    }
  }
  for (uint32_t i = 0U; i < 8U; i++)
  {
    uint32_t *os = hash;
    uint32_t x = hash[i] + hash_old[i];
    os[i] = x;
  }
}

static inline void sha256_update_nblocks(uint32_t len, uint8_t *b, uint32_t *st)
{
  uint32_t blocks = len / 64U;
  for (uint32_t i = 0U; i < blocks; i++)
  {
    uint8_t *b0 = b;
    uint8_t *mb = b0 + i * 64U;
    sha256_update(mb, st);
  }
}

static inline void
sha256_update_last(uint64_t totlen, uint32_t len, uint8_t *b, uint32_t *hash)
{
  uint32_t blocks;
  if (len + 8U + 1U <= 64U)
  {
    blocks = 1U;
  }
  else
  {
    blocks = 2U;
  }
  uint32_t fin = blocks * 64U;
  uint8_t last[128U] = { 0U };
  uint8_t totlen_buf[8U] = { 0U };
  uint64_t total_len_bits = totlen << 3U;
  store64_be(totlen_buf, total_len_bits);
  uint8_t *b0 = b;
  memcpy(last, b0, len * sizeof (uint8_t));
  last[len] = 0x80U;
  memcpy(last + fin - 8U, totlen_buf, 8U * sizeof (uint8_t));
  uint8_t *last00 = last;
  uint8_t *last10 = last + 64U;
  uint8_t *l0 = last00;
  uint8_t *l1 = last10;
  uint8_t *lb0 = l0;
  uint8_t *lb1 = l1;
  uint8_t *last0 = lb0;
  uint8_t *last1 = lb1;
  sha256_update(last0, hash);
  if (blocks > 1U)
  {
    sha256_update(last1, hash);
  }
}

static inline void sha256_finish(uint32_t *st, uint8_t *h)
{
  uint8_t hbuf[32U] = { 0U };
  for (uint32_t i = 0U; i < 8U; i++)
  {
    store32_be(hbuf + i * 4U, st[i]);
  }
  memcpy(h, hbuf, 32U * sizeof (uint8_t));
}

static void sha512_init(uint64_t *hash)
{
  for (uint32_t i = 0U; i < 8U; i++)
  {
    uint64_t *os = hash;
    uint64_t x = Hacl_Impl_SHA2_Generic_h512[i];
    os[i] = x;
  }
}

static inline void sha512_update(uint8_t *b, uint64_t *hash)
{
  uint64_t hash_old[8U] = { 0U };
  uint64_t ws[16U] = { 0U };
  memcpy(hash_old, hash, 8U * sizeof (uint64_t));
  uint8_t *b10 = b;
  uint64_t u = load64_be(b10);
  ws[0U] = u;
  uint64_t u0 = load64_be(b10 + 8U);
  ws[1U] = u0;
  uint64_t u1 = load64_be(b10 + 16U);
  ws[2U] = u1;
  uint64_t u2 = load64_be(b10 + 24U);
  ws[3U] = u2;
  uint64_t u3 = load64_be(b10 + 32U);
  ws[4U] = u3;
  uint64_t u4 = load64_be(b10 + 40U);
  ws[5U] = u4;
  uint64_t u5 = load64_be(b10 + 48U);
  ws[6U] = u5;
  uint64_t u6 = load64_be(b10 + 56U);
  ws[7U] = u6;
  uint64_t u7 = load64_be(b10 + 64U);
  ws[8U] = u7;
  uint64_t u8 = load64_be(b10 + 72U);
  ws[9U] = u8;
  uint64_t u9 = load64_be(b10 + 80U);
  ws[10U] = u9;
  uint64_t u10 = load64_be(b10 + 88U);
  ws[11U] = u10;
  uint64_t u11 = load64_be(b10 + 96U);
  ws[12U] = u11;
  uint64_t u12 = load64_be(b10 + 104U);
  ws[13U] = u12;
  uint64_t u13 = load64_be(b10 + 112U);
  ws[14U] = u13;
  uint64_t u14 = load64_be(b10 + 120U);
  ws[15U] = u14;
  for (uint32_t i0 = 0U; i0 < 5U; i0++)
  {
    for (uint32_t i = 0U; i < 16U; i++)
    {
      uint64_t k_t = Hacl_Impl_SHA2_Generic_k384_512[16U * i0 + i];
      uint64_t ws_t = ws[i];
      uint64_t a0 = hash[0U];
      uint64_t b0 = hash[1U];
      uint64_t c0 = hash[2U];
      uint64_t d0 = hash[3U];
      uint64_t e0 = hash[4U];
      uint64_t f0 = hash[5U];
      uint64_t g0 = hash[6U];
      uint64_t h02 = hash[7U];
      uint64_t k_e_t = k_t;
      uint64_t
      t1 =
        h02
        + ((e0 << 50U | e0 >> 14U) ^ ((e0 << 46U | e0 >> 18U) ^ (e0 << 23U | e0 >> 41U)))
        + ((e0 & f0) ^ (~e0 & g0))
        + k_e_t
        + ws_t;
      uint64_t
      t2 =
        ((a0 << 36U | a0 >> 28U) ^ ((a0 << 30U | a0 >> 34U) ^ (a0 << 25U | a0 >> 39U)))
        + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
      uint64_t a1 = t1 + t2;
      uint64_t b1 = a0;
      uint64_t c1 = b0;
      uint64_t d1 = c0;
      uint64_t e1 = d0 + t1;
      uint64_t f1 = e0;
      uint64_t g1 = f0;
      uint64_t h12 = g0;
      hash[0U] = a1;
      hash[1U] = b1;
      hash[2U] = c1;
      hash[3U] = d1;
      hash[4U] = e1;
      hash[5U] = f1;
      hash[6U] = g1;
      hash[7U] = h12;
    }
    if (i0 < 4U)
    {
      for (uint32_t i = 0U; i < 16U; i++)
      {
        uint64_t t16 = ws[i];
        uint64_t t15 = ws[(i + 1U) % 16U];
        uint64_t t7 = ws[(i + 9U) % 16U];
        uint64_t t2 = ws[(i + 14U) % 16U];
        uint64_t s1 = (t2 << 45U | t2 >> 19U) ^ ((t2 << 3U | t2 >> 61U) ^ t2 >> 6U);
        uint64_t s0 = (t15 << 63U | t15 >> 1U) ^ ((t15 << 56U | t15 >> 8U) ^ t15 >> 7U);
        ws[i] = s1 + t7 + s0 + t16;
      }
    }
  }
  for (uint32_t i = 0U; i < 8U; i++)
  {
    uint64_t *os = hash;
    uint64_t x = hash[i] + hash_old[i];
    os[i] = x;
  }
}

static inline void sha512_update_nblocks(uint32_t len, uint8_t *b, uint64_t *st)
{
  uint32_t blocks = len / 128U;
  for (uint32_t i = 0U; i < blocks; i++)
  {
    uint8_t *b0 = b;
    uint8_t *mb = b0 + i * 128U;
    sha512_update(mb, st);
  }
}

static inline void
sha512_update_last(FStar_UInt128_uint128 totlen, uint32_t len, uint8_t *b, uint64_t *hash)
{
  uint32_t blocks;
  if (len + 16U + 1U <= 128U)
  {
    blocks = 1U;
  }
  else
  {
    blocks = 2U;
  }
  uint32_t fin = blocks * 128U;
  uint8_t last[256U] = { 0U };
  uint8_t totlen_buf[16U] = { 0U };
  FStar_UInt128_uint128 total_len_bits = FStar_UInt128_shift_left(totlen, 3U);
  store128_be(totlen_buf, total_len_bits);
  uint8_t *b0 = b;
  memcpy(last, b0, len * sizeof (uint8_t));
  last[len] = 0x80U;
  memcpy(last + fin - 16U, totlen_buf, 16U * sizeof (uint8_t));
  uint8_t *last00 = last;
  uint8_t *last10 = last + 128U;
  uint8_t *l0 = last00;
  uint8_t *l1 = last10;
  uint8_t *lb0 = l0;
  uint8_t *lb1 = l1;
  uint8_t *last0 = lb0;
  uint8_t *last1 = lb1;
  sha512_update(last0, hash);
  if (blocks > 1U)
  {
    sha512_update(last1, hash);
  }
}

static inline void sha512_finish(uint64_t *st, uint8_t *h)
{
  uint8_t hbuf[64U] = { 0U };
  for (uint32_t i = 0U; i < 8U; i++)
  {
    store64_be(hbuf + i * 8U, st[i]);
  }
  memcpy(h, hbuf, 64U * sizeof (uint8_t));
}

static inline void sha384_init(uint64_t *hash)
{
  for (uint32_t i = 0U; i < 8U; i++)
  {
    uint64_t *os = hash;
    uint64_t x = Hacl_Impl_SHA2_Generic_h384[i];
    os[i] = x;
  }
}

static inline void sha384_update_nblocks(uint32_t len, uint8_t *b, uint64_t *st)
{
  sha512_update_nblocks(len, b, st);
}

static void
sha384_update_last(FStar_UInt128_uint128 totlen, uint32_t len, uint8_t *b, uint64_t *st)
{
  sha512_update_last(totlen, len, b, st);
}

static inline void sha384_finish(uint64_t *st, uint8_t *h)
{
  uint8_t hbuf[64U] = { 0U };
  for (uint32_t i = 0U; i < 8U; i++)
  {
    store64_be(hbuf + i * 8U, st[i]);
  }
  memcpy(h, hbuf, 48U * sizeof (uint8_t));
}

static uint32_t _h0[5U] = { 0x67452301U, 0xefcdab89U, 0x98badcfeU, 0x10325476U, 0xc3d2e1f0U };

static void init(uint32_t *s)
{
  for (uint32_t i = 0U; i < 5U; i++)
  {
    s[i] = _h0[i];
  }
}

static void update(uint32_t *h, uint8_t *l)
{
  uint32_t ha = h[0U];
  uint32_t hb = h[1U];
  uint32_t hc = h[2U];
  uint32_t hd = h[3U];
  uint32_t he = h[4U];
  uint32_t _w[80U] = { 0U };
  for (uint32_t i = 0U; i < 80U; i++)
  {
    uint32_t v;
    if (i < 16U)
    {
      uint8_t *b = l + i * 4U;
      uint32_t u = load32_be(b);
      v = u;
    }
    else
    {
      uint32_t wmit3 = _w[i - 3U];
      uint32_t wmit8 = _w[i - 8U];
      uint32_t wmit14 = _w[i - 14U];
      uint32_t wmit16 = _w[i - 16U];
      v = (wmit3 ^ (wmit8 ^ (wmit14 ^ wmit16))) << 1U | (wmit3 ^ (wmit8 ^ (wmit14 ^ wmit16))) >> 31U;
    }
    _w[i] = v;
  }
  for (uint32_t i = 0U; i < 80U; i++)
  {
    uint32_t _a = h[0U];
    uint32_t _b = h[1U];
    uint32_t _c = h[2U];
    uint32_t _d = h[3U];
    uint32_t _e = h[4U];
    uint32_t wmit = _w[i];
    uint32_t ite0;
    if (i < 20U)
    {
      ite0 = (_b & _c) ^ (~_b & _d);
    }
    else if (39U < i && i < 60U)
    {
      ite0 = (_b & _c) ^ ((_b & _d) ^ (_c & _d));
    }
    else
    {
      ite0 = _b ^ (_c ^ _d);
    }
    uint32_t ite;
    if (i < 20U)
    {
      ite = 0x5a827999U;
    }
    else if (i < 40U)
    {
      ite = 0x6ed9eba1U;
    }
    else if (i < 60U)
    {
      ite = 0x8f1bbcdcU;
    }
    else
    {
      ite = 0xca62c1d6U;
    }
    uint32_t _T = (_a << 5U | _a >> 27U) + ite0 + _e + ite + wmit;
    h[0U] = _T;
    h[1U] = _a;
    h[2U] = _b << 30U | _b >> 2U;
    h[3U] = _c;
    h[4U] = _d;
  }
  for (uint32_t i = 0U; i < 80U; i++)
  {
    _w[i] = 0U;
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

static void pad(uint64_t len, uint8_t *dst)
{
  uint8_t *dst1 = dst;
  dst1[0U] = 0x80U;
  uint8_t *dst2 = dst + 1U;
  for (uint32_t i = 0U; i < (128U - (9U + (uint32_t)(len % (uint64_t)64U))) % 64U; i++)
  {
    dst2[i] = 0U;
  }
  uint8_t *dst3 = dst + 1U + (128U - (9U + (uint32_t)(len % (uint64_t)64U))) % 64U;
  store64_be(dst3, len << 3U);
}

static void finish(uint32_t *s, uint8_t *dst)
{
  for (uint32_t i = 0U; i < 5U; i++)
  {
    store32_be(dst + i * 4U, s[i]);
  }
}

static void update_multi(uint32_t *s, uint8_t *blocks, uint32_t n_blocks)
{
  for (uint32_t i = 0U; i < n_blocks; i++)
  {
    uint32_t sz = 64U;
    uint8_t *block = blocks + sz * i;
    update(s, block);
  }
}

static void update_last(uint32_t *s, uint64_t prev_len, uint8_t *input, uint32_t input_len)
{
  uint32_t blocks_n = input_len / 64U;
  uint32_t blocks_len = blocks_n * 64U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  update_multi(s, blocks, blocks_n);
  uint64_t total_input_len = prev_len + (uint64_t)input_len;
  uint32_t pad_len = 1U + (128U - (9U + (uint32_t)(total_input_len % (uint64_t)64U))) % 64U + 8U;
  uint32_t tmp_len = rest_len + pad_len;
  uint8_t tmp_twoblocks[128U] = { 0U };
  uint8_t *tmp = tmp_twoblocks;
  uint8_t *tmp_rest = tmp;
  uint8_t *tmp_pad = tmp + rest_len;
  memcpy(tmp_rest, rest, rest_len * sizeof (uint8_t));
  pad(total_input_len, tmp_pad);
  update_multi(s, tmp, tmp_len / 64U);
}

static void hash_oneshot(uint8_t *output, uint8_t *input, uint32_t input_len)
{
  uint32_t s[5U] = { 0x67452301U, 0xefcdab89U, 0x98badcfeU, 0x10325476U, 0xc3d2e1f0U };
  uint32_t blocks_n0 = input_len / 64U;
  uint32_t blocks_n1;
  if (input_len % 64U == 0U && blocks_n0 > 0U)
  {
    blocks_n1 = blocks_n0 - 1U;
  }
  else
  {
    blocks_n1 = blocks_n0;
  }
  uint32_t blocks_len0 = blocks_n1 * 64U;
  uint8_t *blocks0 = input;
  uint32_t rest_len0 = input_len - blocks_len0;
  uint8_t *rest0 = input + blocks_len0;
  uint32_t blocks_n = blocks_n1;
  uint32_t blocks_len = blocks_len0;
  uint8_t *blocks = blocks0;
  uint32_t rest_len = rest_len0;
  uint8_t *rest = rest0;
  update_multi(s, blocks, blocks_n);
  update_last(s, (uint64_t)blocks_len, rest, rest_len);
  finish(s, output);
}

/**
Hash `input`, of len `input_len`, into `output`, an array of 32 bytes.
*/
static void hash_256(uint8_t *output, uint8_t *input, uint32_t input_len)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint32_t st[8U] = { 0U };
  sha256_init(st);
  uint32_t rem = input_len % 64U;
  uint64_t len_ = (uint64_t)input_len;
  sha256_update_nblocks(input_len, ib, st);
  uint32_t rem1 = input_len % 64U;
  uint8_t *b0 = ib;
  uint8_t *lb = b0 + input_len - rem1;
  sha256_update_last(len_, rem, lb, st);
  sha256_finish(st, rb);
}

/**
Hash `input`, of len `input_len`, into `output`, an array of 64 bytes.
*/
static void hash_512(uint8_t *output, uint8_t *input, uint32_t input_len)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint64_t st[8U] = { 0U };
  sha512_init(st);
  uint32_t rem = input_len % 128U;
  FStar_UInt128_uint128 len_ = FStar_UInt128_uint64_to_uint128((uint64_t)input_len);
  sha512_update_nblocks(input_len, ib, st);
  uint32_t rem1 = input_len % 128U;
  uint8_t *b0 = ib;
  uint8_t *lb = b0 + input_len - rem1;
  sha512_update_last(len_, rem, lb, st);
  sha512_finish(st, rb);
}

/**
Hash `input`, of len `input_len`, into `output`, an array of 48 bytes.
*/
static void hash_384(uint8_t *output, uint8_t *input, uint32_t input_len)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint64_t st[8U] = { 0U };
  sha384_init(st);
  uint32_t rem = input_len % 128U;
  FStar_UInt128_uint128 len_ = FStar_UInt128_uint64_to_uint128((uint64_t)input_len);
  sha384_update_nblocks(input_len, ib, st);
  uint32_t rem1 = input_len % 128U;
  uint8_t *b0 = ib;
  uint8_t *lb = b0 + input_len - rem1;
  sha384_update_last(len_, rem, lb, st);
  sha384_finish(st, rb);
}

extern void C_String_print(Prims_string uu___);

typedef struct __uint32_t_uint32_t_s
{
  uint32_t fst;
  uint32_t snd;
}
__uint32_t_uint32_t;

/**
Write the HMAC-SHA-1 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 byte.
`dst` must point to 20 bytes of memory.
*/
static void
compute_sha1(uint8_t *dst, uint8_t *key, uint32_t key_len, uint8_t *data, uint32_t data_len)
{
  uint32_t l = 64U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t key_block[l];
  memset(key_block, 0U, l * sizeof (uint8_t));
  uint8_t *nkey = key_block;
  uint32_t ite;
  if (key_len <= 64U)
  {
    ite = key_len;
  }
  else
  {
    ite = 20U;
  }
  uint8_t *zeroes = key_block + ite;
  KRML_MAYBE_UNUSED_VAR(zeroes);
  if (key_len <= 64U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));
  }
  else
  {
    hash_oneshot(nkey, key, key_len);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t ipad[l];
  memset(ipad, 0x36U, l * sizeof (uint8_t));
  for (uint32_t i = 0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = (uint32_t)xi ^ (uint32_t)yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t opad[l];
  memset(opad, 0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = 0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = (uint32_t)xi ^ (uint32_t)yi;
  }
  uint32_t s[5U] = { 0x67452301U, 0xefcdab89U, 0x98badcfeU, 0x10325476U, 0xc3d2e1f0U };
  uint8_t *dst1 = ipad;
  if (data_len == 0U)
  {
    update_last(s, 0ULL, ipad, 64U);
  }
  else
  {
    uint32_t block_len = 64U;
    uint32_t n_blocks0 = data_len / block_len;
    uint32_t rem0 = data_len % block_len;
    __uint32_t_uint32_t scrut;
    if (n_blocks0 > 0U && rem0 == 0U)
    {
      uint32_t n_blocks_ = n_blocks0 - 1U;
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = data_len - n_blocks_ * block_len });
    }
    else
    {
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem0 });
    }
    uint32_t n_blocks = scrut.fst;
    uint32_t rem_len = scrut.snd;
    uint32_t full_blocks_len = n_blocks * block_len;
    uint8_t *full_blocks = data;
    uint8_t *rem = data + full_blocks_len;
    update_multi(s, ipad, 1U);
    update_multi(s, full_blocks, n_blocks);
    update_last(s, (uint64_t)64U + (uint64_t)full_blocks_len, rem, rem_len);
  }
  finish(s, dst1);
  uint8_t *hash1 = ipad;
  init(s);
  uint32_t block_len = 64U;
  uint32_t n_blocks0 = 20U / block_len;
  uint32_t rem0 = 20U % block_len;
  __uint32_t_uint32_t scrut;
  if (n_blocks0 > 0U && rem0 == 0U)
  {
    uint32_t n_blocks_ = n_blocks0 - 1U;
    scrut = ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = 20U - n_blocks_ * block_len });
  }
  else
  {
    scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem0 });
  }
  uint32_t n_blocks = scrut.fst;
  uint32_t rem_len = scrut.snd;
  uint32_t full_blocks_len = n_blocks * block_len;
  uint8_t *full_blocks = hash1;
  uint8_t *rem = hash1 + full_blocks_len;
  update_multi(s, opad, 1U);
  update_multi(s, full_blocks, n_blocks);
  update_last(s, (uint64_t)64U + (uint64_t)full_blocks_len, rem, rem_len);
  finish(s, dst);
}

/**
Write the HMAC-SHA-2-256 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 bytes.
`dst` must point to 32 bytes of memory.
*/
static void
compute_sha2_256(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
)
{
  uint32_t l = 64U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t key_block[l];
  memset(key_block, 0U, l * sizeof (uint8_t));
  uint8_t *nkey = key_block;
  uint32_t ite;
  if (key_len <= 64U)
  {
    ite = key_len;
  }
  else
  {
    ite = 32U;
  }
  uint8_t *zeroes = key_block + ite;
  KRML_MAYBE_UNUSED_VAR(zeroes);
  if (key_len <= 64U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));
  }
  else
  {
    hash_256(nkey, key, key_len);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t ipad[l];
  memset(ipad, 0x36U, l * sizeof (uint8_t));
  for (uint32_t i = 0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = (uint32_t)xi ^ (uint32_t)yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t opad[l];
  memset(opad, 0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = 0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = (uint32_t)xi ^ (uint32_t)yi;
  }
  uint32_t st[8U] = { 0U };
  for (uint32_t i = 0U; i < 8U; i++)
  {
    uint32_t *os = st;
    uint32_t x = Hacl_Impl_SHA2_Generic_h256[i];
    os[i] = x;
  }
  uint32_t *s = st;
  uint8_t *dst1 = ipad;
  if (data_len == 0U)
  {
    sha256_update_last(0ULL + (uint64_t)64U, 64U, ipad, s);
  }
  else
  {
    uint32_t block_len = 64U;
    uint32_t n_blocks0 = data_len / block_len;
    uint32_t rem0 = data_len % block_len;
    __uint32_t_uint32_t scrut;
    if (n_blocks0 > 0U && rem0 == 0U)
    {
      uint32_t n_blocks_ = n_blocks0 - 1U;
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = data_len - n_blocks_ * block_len });
    }
    else
    {
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem0 });
    }
    uint32_t n_blocks = scrut.fst;
    uint32_t rem_len = scrut.snd;
    uint32_t full_blocks_len = n_blocks * block_len;
    uint8_t *full_blocks = data;
    uint8_t *rem = data + full_blocks_len;
    sha256_update_nblocks(64U, ipad, s);
    sha256_update_nblocks(n_blocks * 64U, full_blocks, s);
    sha256_update_last((uint64_t)64U + (uint64_t)full_blocks_len + (uint64_t)rem_len,
      rem_len,
      rem,
      s);
  }
  sha256_finish(s, dst1);
  uint8_t *hash1 = ipad;
  sha256_init(s);
  uint32_t block_len = 64U;
  uint32_t n_blocks0 = 32U / block_len;
  uint32_t rem0 = 32U % block_len;
  __uint32_t_uint32_t scrut;
  if (n_blocks0 > 0U && rem0 == 0U)
  {
    uint32_t n_blocks_ = n_blocks0 - 1U;
    scrut = ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = 32U - n_blocks_ * block_len });
  }
  else
  {
    scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem0 });
  }
  uint32_t n_blocks = scrut.fst;
  uint32_t rem_len = scrut.snd;
  uint32_t full_blocks_len = n_blocks * block_len;
  uint8_t *full_blocks = hash1;
  uint8_t *rem = hash1 + full_blocks_len;
  sha256_update_nblocks(64U, opad, s);
  sha256_update_nblocks(n_blocks * 64U, full_blocks, s);
  sha256_update_last((uint64_t)64U + (uint64_t)full_blocks_len + (uint64_t)rem_len,
    rem_len,
    rem,
    s);
  sha256_finish(s, dst);
}

/**
Write the HMAC-SHA-2-384 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 128 bytes.
`dst` must point to 48 bytes of memory.
*/
static void
compute_sha2_384(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
)
{
  uint32_t l = 128U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t key_block[l];
  memset(key_block, 0U, l * sizeof (uint8_t));
  uint8_t *nkey = key_block;
  uint32_t ite;
  if (key_len <= 128U)
  {
    ite = key_len;
  }
  else
  {
    ite = 48U;
  }
  uint8_t *zeroes = key_block + ite;
  KRML_MAYBE_UNUSED_VAR(zeroes);
  if (key_len <= 128U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));
  }
  else
  {
    hash_384(nkey, key, key_len);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t ipad[l];
  memset(ipad, 0x36U, l * sizeof (uint8_t));
  for (uint32_t i = 0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = (uint32_t)xi ^ (uint32_t)yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t opad[l];
  memset(opad, 0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = 0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = (uint32_t)xi ^ (uint32_t)yi;
  }
  uint64_t st[8U] = { 0U };
  for (uint32_t i = 0U; i < 8U; i++)
  {
    uint64_t *os = st;
    uint64_t x = Hacl_Impl_SHA2_Generic_h384[i];
    os[i] = x;
  }
  uint64_t *s = st;
  uint8_t *dst1 = ipad;
  if (data_len == 0U)
  {
    sha384_update_last(FStar_UInt128_add(FStar_UInt128_uint64_to_uint128(0ULL),
        FStar_UInt128_uint64_to_uint128((uint64_t)128U)),
      128U,
      ipad,
      s);
  }
  else
  {
    uint32_t block_len = 128U;
    uint32_t n_blocks0 = data_len / block_len;
    uint32_t rem0 = data_len % block_len;
    __uint32_t_uint32_t scrut;
    if (n_blocks0 > 0U && rem0 == 0U)
    {
      uint32_t n_blocks_ = n_blocks0 - 1U;
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = data_len - n_blocks_ * block_len });
    }
    else
    {
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem0 });
    }
    uint32_t n_blocks = scrut.fst;
    uint32_t rem_len = scrut.snd;
    uint32_t full_blocks_len = n_blocks * block_len;
    uint8_t *full_blocks = data;
    uint8_t *rem = data + full_blocks_len;
    sha384_update_nblocks(128U, ipad, s);
    sha384_update_nblocks(n_blocks * 128U, full_blocks, s);
    sha384_update_last(FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)128U),
          FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
        FStar_UInt128_uint64_to_uint128((uint64_t)rem_len)),
      rem_len,
      rem,
      s);
  }
  sha384_finish(s, dst1);
  uint8_t *hash1 = ipad;
  sha384_init(s);
  uint32_t block_len = 128U;
  uint32_t n_blocks0 = 48U / block_len;
  uint32_t rem0 = 48U % block_len;
  __uint32_t_uint32_t scrut;
  if (n_blocks0 > 0U && rem0 == 0U)
  {
    uint32_t n_blocks_ = n_blocks0 - 1U;
    scrut = ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = 48U - n_blocks_ * block_len });
  }
  else
  {
    scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem0 });
  }
  uint32_t n_blocks = scrut.fst;
  uint32_t rem_len = scrut.snd;
  uint32_t full_blocks_len = n_blocks * block_len;
  uint8_t *full_blocks = hash1;
  uint8_t *rem = hash1 + full_blocks_len;
  sha384_update_nblocks(128U, opad, s);
  sha384_update_nblocks(n_blocks * 128U, full_blocks, s);
  sha384_update_last(FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)128U),
        FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
      FStar_UInt128_uint64_to_uint128((uint64_t)rem_len)),
    rem_len,
    rem,
    s);
  sha384_finish(s, dst);
}

/**
Write the HMAC-SHA-2-512 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 128 bytes.
`dst` must point to 64 bytes of memory.
*/
static void
compute_sha2_512(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
)
{
  uint32_t l = 128U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t key_block[l];
  memset(key_block, 0U, l * sizeof (uint8_t));
  uint8_t *nkey = key_block;
  uint32_t ite;
  if (key_len <= 128U)
  {
    ite = key_len;
  }
  else
  {
    ite = 64U;
  }
  uint8_t *zeroes = key_block + ite;
  KRML_MAYBE_UNUSED_VAR(zeroes);
  if (key_len <= 128U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));
  }
  else
  {
    hash_512(nkey, key, key_len);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t ipad[l];
  memset(ipad, 0x36U, l * sizeof (uint8_t));
  for (uint32_t i = 0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = (uint32_t)xi ^ (uint32_t)yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t opad[l];
  memset(opad, 0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = 0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = (uint32_t)xi ^ (uint32_t)yi;
  }
  uint64_t st[8U] = { 0U };
  for (uint32_t i = 0U; i < 8U; i++)
  {
    uint64_t *os = st;
    uint64_t x = Hacl_Impl_SHA2_Generic_h512[i];
    os[i] = x;
  }
  uint64_t *s = st;
  uint8_t *dst1 = ipad;
  if (data_len == 0U)
  {
    sha512_update_last(FStar_UInt128_add(FStar_UInt128_uint64_to_uint128(0ULL),
        FStar_UInt128_uint64_to_uint128((uint64_t)128U)),
      128U,
      ipad,
      s);
  }
  else
  {
    uint32_t block_len = 128U;
    uint32_t n_blocks0 = data_len / block_len;
    uint32_t rem0 = data_len % block_len;
    __uint32_t_uint32_t scrut;
    if (n_blocks0 > 0U && rem0 == 0U)
    {
      uint32_t n_blocks_ = n_blocks0 - 1U;
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = data_len - n_blocks_ * block_len });
    }
    else
    {
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem0 });
    }
    uint32_t n_blocks = scrut.fst;
    uint32_t rem_len = scrut.snd;
    uint32_t full_blocks_len = n_blocks * block_len;
    uint8_t *full_blocks = data;
    uint8_t *rem = data + full_blocks_len;
    sha512_update_nblocks(128U, ipad, s);
    sha512_update_nblocks(n_blocks * 128U, full_blocks, s);
    sha512_update_last(FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)128U),
          FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
        FStar_UInt128_uint64_to_uint128((uint64_t)rem_len)),
      rem_len,
      rem,
      s);
  }
  sha512_finish(s, dst1);
  uint8_t *hash1 = ipad;
  sha512_init(s);
  uint32_t block_len = 128U;
  uint32_t n_blocks0 = 64U / block_len;
  uint32_t rem0 = 64U % block_len;
  __uint32_t_uint32_t scrut;
  if (n_blocks0 > 0U && rem0 == 0U)
  {
    uint32_t n_blocks_ = n_blocks0 - 1U;
    scrut = ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = 64U - n_blocks_ * block_len });
  }
  else
  {
    scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem0 });
  }
  uint32_t n_blocks = scrut.fst;
  uint32_t rem_len = scrut.snd;
  uint32_t full_blocks_len = n_blocks * block_len;
  uint8_t *full_blocks = hash1;
  uint8_t *rem = hash1 + full_blocks_len;
  sha512_update_nblocks(128U, opad, s);
  sha512_update_nblocks(n_blocks * 128U, full_blocks, s);
  sha512_update_last(FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)128U),
        FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
      FStar_UInt128_uint64_to_uint128((uint64_t)rem_len)),
    rem_len,
    rem,
    s);
  sha512_finish(s, dst);
}

static bool is_supported_alg(hash_alg uu___)
{
  switch (uu___)
  {
    case SHA1:
      {
        return true;
      }
    case SHA2_256:
      {
        return true;
      }
    case SHA2_384:
      {
        return true;
      }
    case SHA2_512:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

extern void LowStar_Printf_print_string(Prims_string uu___);

extern void LowStar_Printf_print_u32(uint32_t uu___);

extern void LowStar_Printf_print_lmbuffer_u8(uint32_t l, uint8_t *b);

static uint32_t reseed_interval = 1024U;

static uint32_t max_output_length = 65536U;

static uint32_t max_length = 65536U;

static uint32_t max_personalization_string_length = 65536U;

static uint32_t max_additional_input_length = 65536U;

/**
Return the minimal entropy input length of the desired hash function.

@param a Hash algorithm to use.
*/
static uint32_t min_length(hash_alg a)
{
  switch (a)
  {
    case SHA1:
      {
        return 16U;
      }
    case SHA2_256:
      {
        return 32U;
      }
    case SHA2_384:
      {
        return 32U;
      }
    case SHA2_512:
      {
        return 32U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

typedef struct state_s
{
  uint8_t *k;
  uint8_t *v;
  uint32_t *reseed_counter;
}
state;

/**
Instantiate the DRBG.

@param a Hash algorithm to use. (Value must match the value used in `Hacl_HMAC_DRBG_create_in`.)
@param st Pointer to DRBG state.
@param entropy_input_len Length of entropy input.
@param entropy_input Pointer to `entropy_input_len` bytes of memory where entropy input is read from.
@param nonce_len Length of nonce.
@param nonce Pointer to `nonce_len` bytes of memory where nonce is read from.
@param personalization_string_len length of personalization string.
@param personalization_string Pointer to `personalization_string_len` bytes of memory where personalization string is read from.
*/
static void
instantiate(
  hash_alg a,
  state st,
  uint32_t entropy_input_len,
  uint8_t *entropy_input,
  uint32_t nonce_len,
  uint8_t *nonce,
  uint32_t personalization_string_len,
  uint8_t *personalization_string
)
{
  switch (a)
  {
    case SHA1:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t),
          entropy_input_len + nonce_len + personalization_string_len);
        uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
        memset(seed_material,
          0U,
          (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len + nonce_len,
          personalization_string,
          personalization_string_len * sizeof (uint8_t));
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        memset(k, 0U, 20U * sizeof (uint8_t));
        memset(v, 1U, 20U * sizeof (uint8_t));
        ctr[0U] = 1U;
        uint32_t input_len = 21U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, 20U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != 0U)
        {
          memcpy(input0 + 21U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        }
        input0[20U] = 0U;
        compute_sha1(k_, k, 20U, input0, input_len);
        compute_sha1(v, k_, 20U, v, 20U);
        memcpy(k, k_, 20U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != 0U)
        {
          uint32_t input_len0 = 21U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, 20U * sizeof (uint8_t));
          if (entropy_input_len + nonce_len + personalization_string_len != 0U)
          {
            memcpy(input + 21U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
          }
          input[20U] = 1U;
          compute_sha1(k_0, k, 20U, input, input_len0);
          compute_sha1(v, k_0, 20U, v, 20U);
          memcpy(k, k_0, 20U * sizeof (uint8_t));
        }
        break;
      }
    case SHA2_256:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t),
          entropy_input_len + nonce_len + personalization_string_len);
        uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
        memset(seed_material,
          0U,
          (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len + nonce_len,
          personalization_string,
          personalization_string_len * sizeof (uint8_t));
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        memset(k, 0U, 32U * sizeof (uint8_t));
        memset(v, 1U, 32U * sizeof (uint8_t));
        ctr[0U] = 1U;
        uint32_t input_len = 33U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, 32U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != 0U)
        {
          memcpy(input0 + 33U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        }
        input0[32U] = 0U;
        compute_sha2_256(k_, k, 32U, input0, input_len);
        compute_sha2_256(v, k_, 32U, v, 32U);
        memcpy(k, k_, 32U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != 0U)
        {
          uint32_t input_len0 = 33U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, 32U * sizeof (uint8_t));
          if (entropy_input_len + nonce_len + personalization_string_len != 0U)
          {
            memcpy(input + 33U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
          }
          input[32U] = 1U;
          compute_sha2_256(k_0, k, 32U, input, input_len0);
          compute_sha2_256(v, k_0, 32U, v, 32U);
          memcpy(k, k_0, 32U * sizeof (uint8_t));
        }
        break;
      }
    case SHA2_384:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t),
          entropy_input_len + nonce_len + personalization_string_len);
        uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
        memset(seed_material,
          0U,
          (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len + nonce_len,
          personalization_string,
          personalization_string_len * sizeof (uint8_t));
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        memset(k, 0U, 48U * sizeof (uint8_t));
        memset(v, 1U, 48U * sizeof (uint8_t));
        ctr[0U] = 1U;
        uint32_t input_len = 49U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, 48U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != 0U)
        {
          memcpy(input0 + 49U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        }
        input0[48U] = 0U;
        compute_sha2_384(k_, k, 48U, input0, input_len);
        compute_sha2_384(v, k_, 48U, v, 48U);
        memcpy(k, k_, 48U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != 0U)
        {
          uint32_t input_len0 = 49U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, 48U * sizeof (uint8_t));
          if (entropy_input_len + nonce_len + personalization_string_len != 0U)
          {
            memcpy(input + 49U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
          }
          input[48U] = 1U;
          compute_sha2_384(k_0, k, 48U, input, input_len0);
          compute_sha2_384(v, k_0, 48U, v, 48U);
          memcpy(k, k_0, 48U * sizeof (uint8_t));
        }
        break;
      }
    case SHA2_512:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t),
          entropy_input_len + nonce_len + personalization_string_len);
        uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
        memset(seed_material,
          0U,
          (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len, nonce, nonce_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len + nonce_len,
          personalization_string,
          personalization_string_len * sizeof (uint8_t));
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        memset(k, 0U, 64U * sizeof (uint8_t));
        memset(v, 1U, 64U * sizeof (uint8_t));
        ctr[0U] = 1U;
        uint32_t input_len = 65U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, 64U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != 0U)
        {
          memcpy(input0 + 65U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        }
        input0[64U] = 0U;
        compute_sha2_512(k_, k, 64U, input0, input_len);
        compute_sha2_512(v, k_, 64U, v, 64U);
        memcpy(k, k_, 64U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != 0U)
        {
          uint32_t input_len0 = 65U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, 64U * sizeof (uint8_t));
          if (entropy_input_len + nonce_len + personalization_string_len != 0U)
          {
            memcpy(input + 65U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
          }
          input[64U] = 1U;
          compute_sha2_512(k_0, k, 64U, input, input_len0);
          compute_sha2_512(v, k_0, 64U, v, 64U);
          memcpy(k, k_0, 64U * sizeof (uint8_t));
        }
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

/**
Reseed the DRBG.

@param a Hash algorithm to use. (Value must match the value used in `Hacl_HMAC_DRBG_create_in`.)
@param st Pointer to DRBG state.
@param entropy_input_len Length of entropy input.
@param entropy_input Pointer to `entropy_input_len` bytes of memory where entropy input is read from.
@param additional_input_input_len Length of additional input.
@param additional_input_input Pointer to `additional_input_input_len` bytes of memory where additional input is read from.
*/
static void
reseed(
  hash_alg a,
  state st,
  uint32_t entropy_input_len,
  uint8_t *entropy_input,
  uint32_t additional_input_input_len,
  uint8_t *additional_input_input
)
{
  switch (a)
  {
    case SHA1:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_input_len);
        uint8_t seed_material[entropy_input_len + additional_input_input_len];
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len,
          additional_input_input,
          additional_input_input_len * sizeof (uint8_t));
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        uint32_t input_len = 21U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, 20U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          memcpy(input0 + 21U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        }
        input0[20U] = 0U;
        compute_sha1(k_, k, 20U, input0, input_len);
        compute_sha1(v, k_, 20U, v, 20U);
        memcpy(k, k_, 20U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          uint32_t input_len0 = 21U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, 20U * sizeof (uint8_t));
          if (entropy_input_len + additional_input_input_len != 0U)
          {
            memcpy(input + 21U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
          }
          input[20U] = 1U;
          compute_sha1(k_0, k, 20U, input, input_len0);
          compute_sha1(v, k_0, 20U, v, 20U);
          memcpy(k, k_0, 20U * sizeof (uint8_t));
        }
        ctr[0U] = 1U;
        break;
      }
    case SHA2_256:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_input_len);
        uint8_t seed_material[entropy_input_len + additional_input_input_len];
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len,
          additional_input_input,
          additional_input_input_len * sizeof (uint8_t));
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        uint32_t input_len = 33U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, 32U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          memcpy(input0 + 33U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        }
        input0[32U] = 0U;
        compute_sha2_256(k_, k, 32U, input0, input_len);
        compute_sha2_256(v, k_, 32U, v, 32U);
        memcpy(k, k_, 32U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          uint32_t input_len0 = 33U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, 32U * sizeof (uint8_t));
          if (entropy_input_len + additional_input_input_len != 0U)
          {
            memcpy(input + 33U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
          }
          input[32U] = 1U;
          compute_sha2_256(k_0, k, 32U, input, input_len0);
          compute_sha2_256(v, k_0, 32U, v, 32U);
          memcpy(k, k_0, 32U * sizeof (uint8_t));
        }
        ctr[0U] = 1U;
        break;
      }
    case SHA2_384:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_input_len);
        uint8_t seed_material[entropy_input_len + additional_input_input_len];
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len,
          additional_input_input,
          additional_input_input_len * sizeof (uint8_t));
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        uint32_t input_len = 49U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, 48U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          memcpy(input0 + 49U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        }
        input0[48U] = 0U;
        compute_sha2_384(k_, k, 48U, input0, input_len);
        compute_sha2_384(v, k_, 48U, v, 48U);
        memcpy(k, k_, 48U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          uint32_t input_len0 = 49U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, 48U * sizeof (uint8_t));
          if (entropy_input_len + additional_input_input_len != 0U)
          {
            memcpy(input + 49U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
          }
          input[48U] = 1U;
          compute_sha2_384(k_0, k, 48U, input, input_len0);
          compute_sha2_384(v, k_0, 48U, v, 48U);
          memcpy(k, k_0, 48U * sizeof (uint8_t));
        }
        ctr[0U] = 1U;
        break;
      }
    case SHA2_512:
      {
        KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + additional_input_input_len);
        uint8_t seed_material[entropy_input_len + additional_input_input_len];
        memset(seed_material,
          0U,
          (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        memcpy(seed_material, entropy_input, entropy_input_len * sizeof (uint8_t));
        memcpy(seed_material + entropy_input_len,
          additional_input_input,
          additional_input_input_len * sizeof (uint8_t));
        uint8_t *k = st.k;
        uint8_t *v = st.v;
        uint32_t *ctr = st.reseed_counter;
        uint32_t input_len = 65U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, 64U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          memcpy(input0 + 65U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        }
        input0[64U] = 0U;
        compute_sha2_512(k_, k, 64U, input0, input_len);
        compute_sha2_512(v, k_, 64U, v, 64U);
        memcpy(k, k_, 64U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != 0U)
        {
          uint32_t input_len0 = 65U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, 64U * sizeof (uint8_t));
          if (entropy_input_len + additional_input_input_len != 0U)
          {
            memcpy(input + 65U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
          }
          input[64U] = 1U;
          compute_sha2_512(k_0, k, 64U, input, input_len0);
          compute_sha2_512(v, k_0, 64U, v, 64U);
          memcpy(k, k_0, 64U * sizeof (uint8_t));
        }
        ctr[0U] = 1U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

/**
Generate output.

@param a Hash algorithm to use. (Value must match the value used in `create_in`.)
@param output Pointer to `n` bytes of memory where random output is written to.
@param st Pointer to DRBG state.
@param n Length of desired output.
@param additional_input_input_len Length of additional input.
@param additional_input_input Pointer to `additional_input_input_len` bytes of memory where additional input is read from.
*/
static bool
generate(
  hash_alg a,
  uint8_t *output,
  state st,
  uint32_t n,
  uint32_t additional_input_len,
  uint8_t *additional_input
)
{
  switch (a)
  {
    case SHA1:
      {
        if (st.reseed_counter[0U] > reseed_interval)
        {
          return false;
        }
        else
        {
          uint8_t *k = st.k;
          uint8_t *v = st.v;
          uint32_t *ctr = st.reseed_counter;
          if (additional_input_len > 0U)
          {
            uint32_t input_len = 21U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
            uint8_t input0[input_len];
            memset(input0, 0U, input_len * sizeof (uint8_t));
            uint8_t *k_ = input0;
            memcpy(k_, v, 20U * sizeof (uint8_t));
            if (additional_input_len != 0U)
            {
              memcpy(input0 + 21U, additional_input, additional_input_len * sizeof (uint8_t));
            }
            input0[20U] = 0U;
            compute_sha1(k_, k, 20U, input0, input_len);
            compute_sha1(v, k_, 20U, v, 20U);
            memcpy(k, k_, 20U * sizeof (uint8_t));
            if (additional_input_len != 0U)
            {
              uint32_t input_len0 = 21U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
              uint8_t input[input_len0];
              memset(input, 0U, input_len0 * sizeof (uint8_t));
              uint8_t *k_0 = input;
              memcpy(k_0, v, 20U * sizeof (uint8_t));
              if (additional_input_len != 0U)
              {
                memcpy(input + 21U, additional_input, additional_input_len * sizeof (uint8_t));
              }
              input[20U] = 1U;
              compute_sha1(k_0, k, 20U, input, input_len0);
              compute_sha1(v, k_0, 20U, v, 20U);
              memcpy(k, k_0, 20U * sizeof (uint8_t));
            }
          }
          uint8_t *output1 = output;
          uint32_t max = n / 20U;
          uint8_t *out = output1;
          for (uint32_t i = 0U; i < max; i++)
          {
            compute_sha1(v, k, 20U, v, 20U);
            memcpy(out + i * 20U, v, 20U * sizeof (uint8_t));
          }
          if (max * 20U < n)
          {
            uint8_t *block = output1 + max * 20U;
            compute_sha1(v, k, 20U, v, 20U);
            memcpy(block, v, (n - max * 20U) * sizeof (uint8_t));
          }
          uint32_t input_len = 21U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t input0[input_len];
          memset(input0, 0U, input_len * sizeof (uint8_t));
          uint8_t *k_ = input0;
          memcpy(k_, v, 20U * sizeof (uint8_t));
          if (additional_input_len != 0U)
          {
            memcpy(input0 + 21U, additional_input, additional_input_len * sizeof (uint8_t));
          }
          input0[20U] = 0U;
          compute_sha1(k_, k, 20U, input0, input_len);
          compute_sha1(v, k_, 20U, v, 20U);
          memcpy(k, k_, 20U * sizeof (uint8_t));
          if (additional_input_len != 0U)
          {
            uint32_t input_len0 = 21U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t input[input_len0];
            memset(input, 0U, input_len0 * sizeof (uint8_t));
            uint8_t *k_0 = input;
            memcpy(k_0, v, 20U * sizeof (uint8_t));
            if (additional_input_len != 0U)
            {
              memcpy(input + 21U, additional_input, additional_input_len * sizeof (uint8_t));
            }
            input[20U] = 1U;
            compute_sha1(k_0, k, 20U, input, input_len0);
            compute_sha1(v, k_0, 20U, v, 20U);
            memcpy(k, k_0, 20U * sizeof (uint8_t));
          }
          uint32_t old_ctr = ctr[0U];
          ctr[0U] = old_ctr + 1U;
          return true;
        }
        break;
      }
    case SHA2_256:
      {
        if (st.reseed_counter[0U] > reseed_interval)
        {
          return false;
        }
        else
        {
          uint8_t *k = st.k;
          uint8_t *v = st.v;
          uint32_t *ctr = st.reseed_counter;
          if (additional_input_len > 0U)
          {
            uint32_t input_len = 33U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
            uint8_t input0[input_len];
            memset(input0, 0U, input_len * sizeof (uint8_t));
            uint8_t *k_ = input0;
            memcpy(k_, v, 32U * sizeof (uint8_t));
            if (additional_input_len != 0U)
            {
              memcpy(input0 + 33U, additional_input, additional_input_len * sizeof (uint8_t));
            }
            input0[32U] = 0U;
            compute_sha2_256(k_, k, 32U, input0, input_len);
            compute_sha2_256(v, k_, 32U, v, 32U);
            memcpy(k, k_, 32U * sizeof (uint8_t));
            if (additional_input_len != 0U)
            {
              uint32_t input_len0 = 33U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
              uint8_t input[input_len0];
              memset(input, 0U, input_len0 * sizeof (uint8_t));
              uint8_t *k_0 = input;
              memcpy(k_0, v, 32U * sizeof (uint8_t));
              if (additional_input_len != 0U)
              {
                memcpy(input + 33U, additional_input, additional_input_len * sizeof (uint8_t));
              }
              input[32U] = 1U;
              compute_sha2_256(k_0, k, 32U, input, input_len0);
              compute_sha2_256(v, k_0, 32U, v, 32U);
              memcpy(k, k_0, 32U * sizeof (uint8_t));
            }
          }
          uint8_t *output1 = output;
          uint32_t max = n / 32U;
          uint8_t *out = output1;
          for (uint32_t i = 0U; i < max; i++)
          {
            compute_sha2_256(v, k, 32U, v, 32U);
            memcpy(out + i * 32U, v, 32U * sizeof (uint8_t));
          }
          if (max * 32U < n)
          {
            uint8_t *block = output1 + max * 32U;
            compute_sha2_256(v, k, 32U, v, 32U);
            memcpy(block, v, (n - max * 32U) * sizeof (uint8_t));
          }
          uint32_t input_len = 33U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t input0[input_len];
          memset(input0, 0U, input_len * sizeof (uint8_t));
          uint8_t *k_ = input0;
          memcpy(k_, v, 32U * sizeof (uint8_t));
          if (additional_input_len != 0U)
          {
            memcpy(input0 + 33U, additional_input, additional_input_len * sizeof (uint8_t));
          }
          input0[32U] = 0U;
          compute_sha2_256(k_, k, 32U, input0, input_len);
          compute_sha2_256(v, k_, 32U, v, 32U);
          memcpy(k, k_, 32U * sizeof (uint8_t));
          if (additional_input_len != 0U)
          {
            uint32_t input_len0 = 33U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t input[input_len0];
            memset(input, 0U, input_len0 * sizeof (uint8_t));
            uint8_t *k_0 = input;
            memcpy(k_0, v, 32U * sizeof (uint8_t));
            if (additional_input_len != 0U)
            {
              memcpy(input + 33U, additional_input, additional_input_len * sizeof (uint8_t));
            }
            input[32U] = 1U;
            compute_sha2_256(k_0, k, 32U, input, input_len0);
            compute_sha2_256(v, k_0, 32U, v, 32U);
            memcpy(k, k_0, 32U * sizeof (uint8_t));
          }
          uint32_t old_ctr = ctr[0U];
          ctr[0U] = old_ctr + 1U;
          return true;
        }
        break;
      }
    case SHA2_384:
      {
        if (st.reseed_counter[0U] > reseed_interval)
        {
          return false;
        }
        else
        {
          uint8_t *k = st.k;
          uint8_t *v = st.v;
          uint32_t *ctr = st.reseed_counter;
          if (additional_input_len > 0U)
          {
            uint32_t input_len = 49U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
            uint8_t input0[input_len];
            memset(input0, 0U, input_len * sizeof (uint8_t));
            uint8_t *k_ = input0;
            memcpy(k_, v, 48U * sizeof (uint8_t));
            if (additional_input_len != 0U)
            {
              memcpy(input0 + 49U, additional_input, additional_input_len * sizeof (uint8_t));
            }
            input0[48U] = 0U;
            compute_sha2_384(k_, k, 48U, input0, input_len);
            compute_sha2_384(v, k_, 48U, v, 48U);
            memcpy(k, k_, 48U * sizeof (uint8_t));
            if (additional_input_len != 0U)
            {
              uint32_t input_len0 = 49U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
              uint8_t input[input_len0];
              memset(input, 0U, input_len0 * sizeof (uint8_t));
              uint8_t *k_0 = input;
              memcpy(k_0, v, 48U * sizeof (uint8_t));
              if (additional_input_len != 0U)
              {
                memcpy(input + 49U, additional_input, additional_input_len * sizeof (uint8_t));
              }
              input[48U] = 1U;
              compute_sha2_384(k_0, k, 48U, input, input_len0);
              compute_sha2_384(v, k_0, 48U, v, 48U);
              memcpy(k, k_0, 48U * sizeof (uint8_t));
            }
          }
          uint8_t *output1 = output;
          uint32_t max = n / 48U;
          uint8_t *out = output1;
          for (uint32_t i = 0U; i < max; i++)
          {
            compute_sha2_384(v, k, 48U, v, 48U);
            memcpy(out + i * 48U, v, 48U * sizeof (uint8_t));
          }
          if (max * 48U < n)
          {
            uint8_t *block = output1 + max * 48U;
            compute_sha2_384(v, k, 48U, v, 48U);
            memcpy(block, v, (n - max * 48U) * sizeof (uint8_t));
          }
          uint32_t input_len = 49U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t input0[input_len];
          memset(input0, 0U, input_len * sizeof (uint8_t));
          uint8_t *k_ = input0;
          memcpy(k_, v, 48U * sizeof (uint8_t));
          if (additional_input_len != 0U)
          {
            memcpy(input0 + 49U, additional_input, additional_input_len * sizeof (uint8_t));
          }
          input0[48U] = 0U;
          compute_sha2_384(k_, k, 48U, input0, input_len);
          compute_sha2_384(v, k_, 48U, v, 48U);
          memcpy(k, k_, 48U * sizeof (uint8_t));
          if (additional_input_len != 0U)
          {
            uint32_t input_len0 = 49U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t input[input_len0];
            memset(input, 0U, input_len0 * sizeof (uint8_t));
            uint8_t *k_0 = input;
            memcpy(k_0, v, 48U * sizeof (uint8_t));
            if (additional_input_len != 0U)
            {
              memcpy(input + 49U, additional_input, additional_input_len * sizeof (uint8_t));
            }
            input[48U] = 1U;
            compute_sha2_384(k_0, k, 48U, input, input_len0);
            compute_sha2_384(v, k_0, 48U, v, 48U);
            memcpy(k, k_0, 48U * sizeof (uint8_t));
          }
          uint32_t old_ctr = ctr[0U];
          ctr[0U] = old_ctr + 1U;
          return true;
        }
        break;
      }
    case SHA2_512:
      {
        if (st.reseed_counter[0U] > reseed_interval)
        {
          return false;
        }
        else
        {
          uint8_t *k = st.k;
          uint8_t *v = st.v;
          uint32_t *ctr = st.reseed_counter;
          if (additional_input_len > 0U)
          {
            uint32_t input_len = 65U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
            uint8_t input0[input_len];
            memset(input0, 0U, input_len * sizeof (uint8_t));
            uint8_t *k_ = input0;
            memcpy(k_, v, 64U * sizeof (uint8_t));
            if (additional_input_len != 0U)
            {
              memcpy(input0 + 65U, additional_input, additional_input_len * sizeof (uint8_t));
            }
            input0[64U] = 0U;
            compute_sha2_512(k_, k, 64U, input0, input_len);
            compute_sha2_512(v, k_, 64U, v, 64U);
            memcpy(k, k_, 64U * sizeof (uint8_t));
            if (additional_input_len != 0U)
            {
              uint32_t input_len0 = 65U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
              uint8_t input[input_len0];
              memset(input, 0U, input_len0 * sizeof (uint8_t));
              uint8_t *k_0 = input;
              memcpy(k_0, v, 64U * sizeof (uint8_t));
              if (additional_input_len != 0U)
              {
                memcpy(input + 65U, additional_input, additional_input_len * sizeof (uint8_t));
              }
              input[64U] = 1U;
              compute_sha2_512(k_0, k, 64U, input, input_len0);
              compute_sha2_512(v, k_0, 64U, v, 64U);
              memcpy(k, k_0, 64U * sizeof (uint8_t));
            }
          }
          uint8_t *output1 = output;
          uint32_t max = n / 64U;
          uint8_t *out = output1;
          for (uint32_t i = 0U; i < max; i++)
          {
            compute_sha2_512(v, k, 64U, v, 64U);
            memcpy(out + i * 64U, v, 64U * sizeof (uint8_t));
          }
          if (max * 64U < n)
          {
            uint8_t *block = output1 + max * 64U;
            compute_sha2_512(v, k, 64U, v, 64U);
            memcpy(block, v, (n - max * 64U) * sizeof (uint8_t));
          }
          uint32_t input_len = 65U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t input0[input_len];
          memset(input0, 0U, input_len * sizeof (uint8_t));
          uint8_t *k_ = input0;
          memcpy(k_, v, 64U * sizeof (uint8_t));
          if (additional_input_len != 0U)
          {
            memcpy(input0 + 65U, additional_input, additional_input_len * sizeof (uint8_t));
          }
          input0[64U] = 0U;
          compute_sha2_512(k_, k, 64U, input0, input_len);
          compute_sha2_512(v, k_, 64U, v, 64U);
          memcpy(k, k_, 64U * sizeof (uint8_t));
          if (additional_input_len != 0U)
          {
            uint32_t input_len0 = 65U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t input[input_len0];
            memset(input, 0U, input_len0 * sizeof (uint8_t));
            uint8_t *k_0 = input;
            memcpy(k_0, v, 64U * sizeof (uint8_t));
            if (additional_input_len != 0U)
            {
              memcpy(input + 65U, additional_input, additional_input_len * sizeof (uint8_t));
            }
            input[64U] = 1U;
            compute_sha2_512(k_0, k, 64U, input, input_len0);
            compute_sha2_512(v, k_0, 64U, v, 64U);
            memcpy(k, k_0, 64U * sizeof (uint8_t));
          }
          uint32_t old_ctr = ctr[0U];
          ctr[0U] = old_ctr + 1U;
          return true;
        }
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static uint8_t
vectors_low0[16U] =
  { 124U, 173U, 101U, 229U, 204U, 40U, 136U, 174U, 78U, 150U, 15U, 93U, 20U, 60U, 20U, 37U };

static uint8_t vectors_low1[8U] = { 252U, 7U, 133U, 219U, 71U, 28U, 197U, 94U };

static uint8_t
vectors_low2[16U] =
  { 102U, 69U, 29U, 41U, 207U, 101U, 216U, 153U, 162U, 129U, 144U, 95U, 249U, 178U, 158U, 135U };

static uint8_t
vectors_low3[16U] =
  { 128U, 13U, 88U, 59U, 37U, 96U, 210U, 162U, 48U, 1U, 50U, 238U, 45U, 19U, 241U, 159U };

static uint8_t
vectors_low4[16U] =
  { 66U, 234U, 231U, 5U, 194U, 34U, 93U, 33U, 47U, 160U, 85U, 74U, 198U, 172U, 86U, 75U };

static uint8_t
vectors_low5[16U] =
  { 114U, 8U, 30U, 126U, 112U, 32U, 15U, 25U, 130U, 195U, 173U, 156U, 177U, 211U, 221U, 190U };

static uint8_t
vectors_low6[80U] =
  {
    149U, 62U, 146U, 37U, 139U, 231U, 255U, 97U, 185U, 112U, 119U, 37U, 42U, 185U, 131U, 82U, 49U,
    227U, 102U, 223U, 165U, 182U, 53U, 251U, 136U, 156U, 51U, 117U, 98U, 162U, 100U, 29U, 58U, 169U,
    228U, 111U, 238U, 178U, 164U, 234U, 3U, 203U, 115U, 241U, 248U, 1U, 89U, 76U, 60U, 199U, 29U,
    41U, 69U, 193U, 26U, 82U, 187U, 14U, 147U, 65U, 157U, 245U, 208U, 133U, 74U, 213U, 242U, 227U,
    109U, 34U, 60U, 17U, 158U, 20U, 92U, 173U, 80U, 116U, 149U, 167U
  };

static uint8_t
vectors_low7[16U] =
  { 7U, 54U, 160U, 131U, 89U, 90U, 131U, 151U, 203U, 158U, 103U, 108U, 179U, 123U, 251U, 90U };

static uint8_t vectors_low8[8U] = { 11U, 24U, 74U, 109U, 10U, 99U, 10U, 187U };

static uint8_t
vectors_low9[16U] =
  { 195U, 2U, 80U, 61U, 134U, 162U, 189U, 228U, 106U, 12U, 99U, 86U, 26U, 134U, 207U, 217U };

static uint8_t
vectors_low10[16U] =
  { 75U, 80U, 151U, 112U, 51U, 72U, 50U, 119U, 100U, 121U, 69U, 255U, 239U, 161U, 9U, 226U };

static uint8_t
vectors_low11[16U] =
  { 77U, 173U, 129U, 55U, 68U, 245U, 67U, 36U, 179U, 4U, 106U, 133U, 190U, 60U, 195U, 200U };

static uint8_t
vectors_low12[16U] =
  { 116U, 65U, 254U, 250U, 96U, 247U, 238U, 72U, 255U, 56U, 123U, 88U, 126U, 252U, 179U, 230U };

static uint8_t
vectors_low13[16U] =
  { 240U, 208U, 5U, 40U, 154U, 157U, 57U, 147U, 196U, 75U, 183U, 80U, 217U, 108U, 193U, 188U };

static uint8_t
vectors_low14[80U] =
  {
    192U, 57U, 113U, 137U, 123U, 133U, 69U, 133U, 153U, 78U, 235U, 142U, 61U, 107U, 85U, 110U, 26U,
    141U, 241U, 138U, 127U, 248U, 143U, 131U, 232U, 254U, 23U, 230U, 221U, 144U, 113U, 7U, 10U,
    109U, 190U, 246U, 124U, 182U, 18U, 172U, 241U, 34U, 202U, 167U, 248U, 23U, 112U, 75U, 62U, 252U,
    110U, 27U, 31U, 214U, 195U, 48U, 224U, 167U, 50U, 171U, 234U, 147U, 192U, 8U, 24U, 225U, 44U,
    80U, 79U, 216U, 224U, 179U, 108U, 136U, 248U, 74U, 149U, 180U, 147U, 98U
  };

static uint8_t
vectors_low15[16U] =
  { 23U, 32U, 84U, 200U, 39U, 170U, 137U, 95U, 161U, 35U, 155U, 122U, 72U, 71U, 82U, 242U };

static uint8_t vectors_low16[8U] = { 237U, 178U, 114U, 192U, 169U, 140U, 117U, 146U };

static uint8_t
vectors_low17[16U] =
  { 71U, 188U, 120U, 191U, 189U, 27U, 183U, 226U, 220U, 219U, 244U, 235U, 228U, 44U, 82U, 147U };

static uint8_t
vectors_low18[16U] =
  { 41U, 249U, 42U, 14U, 93U, 36U, 225U, 154U, 246U, 152U, 135U, 127U, 105U, 160U, 239U, 181U };

static uint8_t
vectors_low19[80U] =
  {
    100U, 100U, 189U, 174U, 210U, 50U, 69U, 219U, 31U, 101U, 16U, 248U, 101U, 158U, 27U, 25U, 136U,
    29U, 96U, 98U, 32U, 153U, 123U, 131U, 118U, 132U, 167U, 248U, 138U, 22U, 108U, 183U, 92U, 230U,
    130U, 156U, 179U, 241U, 30U, 85U, 210U, 183U, 173U, 52U, 156U, 193U, 244U, 186U, 2U, 227U, 10U,
    118U, 249U, 112U, 97U, 58U, 167U, 70U, 53U, 176U, 3U, 79U, 142U, 152U, 92U, 222U, 79U, 31U,
    221U, 185U, 100U, 101U, 122U, 22U, 147U, 134U, 226U, 7U, 103U, 209U
  };

static uint8_t
vectors_low20[16U] =
  { 177U, 161U, 155U, 176U, 124U, 48U, 202U, 79U, 73U, 220U, 105U, 19U, 13U, 35U, 192U, 167U };

static uint8_t vectors_low21[8U] = { 44U, 6U, 6U, 114U, 151U, 5U, 142U, 197U };

static uint8_t
vectors_low22[16U] =
  { 132U, 8U, 2U, 206U, 162U, 229U, 90U, 59U, 30U, 72U, 123U, 183U, 174U, 230U, 43U, 66U };

static uint8_t
vectors_low23[80U] =
  {
    244U, 27U, 183U, 174U, 83U, 35U, 68U, 169U, 13U, 65U, 59U, 102U, 169U, 78U, 225U, 208U, 37U,
    74U, 93U, 94U, 151U, 78U, 54U, 177U, 153U, 59U, 16U, 66U, 88U, 111U, 84U, 114U, 141U, 30U, 187U,
    124U, 93U, 53U, 21U, 88U, 237U, 103U, 81U, 119U, 228U, 50U, 54U, 7U, 8U, 192U, 8U, 152U, 76U,
    65U, 188U, 76U, 130U, 141U, 131U, 221U, 236U, 169U, 239U, 142U, 205U, 157U, 168U, 128U, 161U,
    53U, 64U, 10U, 67U, 249U, 31U, 76U, 166U, 213U, 157U
  };

static uint8_t
vectors_low24[16U] =
  { 52U, 63U, 157U, 222U, 137U, 169U, 227U, 236U, 196U, 249U, 101U, 60U, 139U, 57U, 45U, 171U };

static uint8_t vectors_low25[8U] = { 196U, 251U, 54U, 6U, 216U, 246U, 45U, 177U };

static uint8_t
vectors_low26[16U] =
  { 2U, 31U, 195U, 234U, 212U, 111U, 248U, 189U, 163U, 183U, 151U, 1U, 183U, 137U, 58U, 57U };

static uint8_t
vectors_low27[16U] =
  { 137U, 24U, 131U, 30U, 21U, 212U, 48U, 97U, 111U, 75U, 217U, 16U, 70U, 254U, 9U, 48U };

static uint8_t
vectors_low28[16U] =
  { 168U, 119U, 35U, 4U, 161U, 172U, 203U, 22U, 102U, 34U, 24U, 167U, 72U, 187U, 79U, 216U };

static uint8_t
vectors_low29[16U] =
  { 75U, 249U, 242U, 185U, 209U, 94U, 195U, 7U, 31U, 243U, 103U, 74U, 215U, 65U, 135U, 89U };

static uint8_t
vectors_low30[80U] =
  {
    151U, 130U, 178U, 17U, 28U, 152U, 91U, 202U, 171U, 11U, 137U, 5U, 173U, 155U, 203U, 151U, 235U,
    63U, 53U, 84U, 198U, 141U, 121U, 238U, 92U, 161U, 220U, 251U, 208U, 215U, 133U, 15U, 101U, 9U,
    12U, 121U, 210U, 29U, 28U, 98U, 83U, 207U, 73U, 63U, 8U, 57U, 44U, 251U, 96U, 70U, 31U, 188U,
    32U, 190U, 180U, 207U, 62U, 2U, 33U, 35U, 129U, 111U, 11U, 197U, 151U, 171U, 235U, 199U, 117U,
    99U, 61U, 179U, 36U, 199U, 193U, 199U, 205U, 94U, 140U, 86U
  };

static uint8_t
vectors_low31[16U] =
  { 10U, 8U, 103U, 38U, 246U, 111U, 42U, 201U, 231U, 218U, 166U, 25U, 8U, 246U, 51U, 25U };

static uint8_t vectors_low32[8U] = { 222U, 191U, 1U, 29U, 64U, 106U, 91U, 35U };

static uint8_t
vectors_low33[16U] =
  { 88U, 88U, 45U, 167U, 79U, 143U, 145U, 219U, 4U, 68U, 190U, 174U, 57U, 1U, 104U, 87U };

static uint8_t
vectors_low34[16U] =
  { 201U, 43U, 162U, 144U, 10U, 176U, 164U, 202U, 53U, 83U, 128U, 99U, 146U, 182U, 179U, 229U };

static uint8_t
vectors_low35[16U] =
  { 86U, 4U, 167U, 110U, 116U, 239U, 75U, 48U, 68U, 102U, 242U, 29U, 245U, 124U, 112U, 243U };

static uint8_t
vectors_low36[16U] =
  { 225U, 228U, 208U, 117U, 76U, 195U, 6U, 161U, 117U, 43U, 80U, 197U, 196U, 70U, 163U, 208U };

static uint8_t
vectors_low37[16U] =
  { 113U, 218U, 207U, 97U, 135U, 92U, 191U, 54U, 85U, 228U, 247U, 210U, 224U, 129U, 212U, 147U };

static uint8_t
vectors_low38[80U] =
  {
    175U, 187U, 58U, 5U, 231U, 83U, 246U, 235U, 240U, 38U, 89U, 74U, 3U, 178U, 43U, 63U, 3U, 46U,
    219U, 135U, 59U, 158U, 30U, 34U, 83U, 46U, 54U, 10U, 9U, 125U, 126U, 13U, 69U, 133U, 187U, 248U,
    47U, 155U, 18U, 215U, 168U, 134U, 48U, 239U, 202U, 222U, 184U, 255U, 220U, 139U, 124U, 138U,
    83U, 254U, 148U, 238U, 169U, 210U, 205U, 108U, 249U, 8U, 40U, 195U, 81U, 31U, 201U, 54U, 34U,
    43U, 168U, 69U, 252U, 119U, 153U, 90U, 3U, 133U, 85U, 120U
  };

static uint8_t
vectors_low39[32U] =
  {
    20U, 104U, 62U, 197U, 8U, 162U, 157U, 120U, 18U, 224U, 240U, 74U, 62U, 157U, 135U, 137U, 112U,
    0U, 220U, 7U, 180U, 251U, 207U, 218U, 88U, 235U, 124U, 218U, 188U, 73U, 46U, 88U
  };

static uint8_t
vectors_low40[16U] =
  { 178U, 36U, 62U, 116U, 78U, 185U, 128U, 179U, 236U, 226U, 92U, 231U, 99U, 131U, 253U, 70U };

static uint8_t
vectors_low41[32U] =
  {
    24U, 89U, 14U, 14U, 244U, 238U, 43U, 218U, 228U, 98U, 247U, 109U, 147U, 36U, 179U, 0U, 37U, 89U,
    247U, 76U, 55U, 12U, 252U, 207U, 150U, 165U, 113U, 214U, 149U, 87U, 3U, 167U
  };

static uint8_t
vectors_low42[32U] =
  {
    158U, 163U, 204U, 202U, 30U, 141U, 121U, 29U, 34U, 252U, 218U, 98U, 31U, 196U, 213U, 27U, 136U,
    45U, 243U, 45U, 148U, 234U, 143U, 32U, 238U, 68U, 147U, 19U, 230U, 144U, 155U, 120U
  };

static uint8_t
vectors_low43[32U] =
  {
    22U, 54U, 106U, 87U, 139U, 94U, 164U, 208U, 203U, 84U, 119U, 144U, 239U, 91U, 79U, 212U, 93U,
    124U, 216U, 69U, 188U, 138U, 124U, 69U, 233U, 148U, 25U, 200U, 115U, 125U, 235U, 180U
  };

static uint8_t
vectors_low44[32U] =
  {
    166U, 140U, 170U, 41U, 165U, 63U, 27U, 168U, 87U, 228U, 132U, 208U, 149U, 128U, 93U, 195U, 25U,
    254U, 105U, 99U, 228U, 196U, 218U, 175U, 53U, 95U, 114U, 46U, 186U, 116U, 107U, 146U
  };

static uint8_t
vectors_low45[128U] =
  {
    196U, 231U, 83U, 46U, 232U, 22U, 120U, 156U, 45U, 61U, 169U, 255U, 159U, 75U, 55U, 19U, 154U,
    133U, 21U, 219U, 248U, 249U, 225U, 208U, 191U, 0U, 193U, 42U, 221U, 215U, 158U, 187U, 215U, 98U,
    54U, 247U, 95U, 42U, 167U, 5U, 160U, 159U, 121U, 85U, 3U, 142U, 191U, 240U, 213U, 102U, 145U,
    28U, 94U, 161U, 50U, 20U, 226U, 194U, 238U, 180U, 109U, 35U, 173U, 134U, 163U, 59U, 96U, 247U,
    185U, 68U, 141U, 99U, 238U, 195U, 225U, 213U, 159U, 72U, 179U, 149U, 82U, 133U, 116U, 71U, 220U,
    93U, 121U, 68U, 102U, 122U, 35U, 14U, 61U, 191U, 163U, 12U, 163U, 34U, 246U, 234U, 202U, 247U,
    83U, 106U, 40U, 103U, 6U, 166U, 39U, 197U, 8U, 60U, 50U, 222U, 6U, 88U, 185U, 7U, 56U, 87U,
    195U, 15U, 177U, 216U, 110U, 184U, 173U, 27U
  };

static uint8_t
vectors_low46[32U] =
  {
    161U, 213U, 187U, 125U, 112U, 98U, 29U, 238U, 107U, 102U, 139U, 40U, 197U, 109U, 86U, 16U, 194U,
    248U, 206U, 211U, 2U, 132U, 204U, 62U, 14U, 72U, 222U, 51U, 26U, 240U, 80U, 98U
  };

static uint8_t
vectors_low47[16U] =
  { 136U, 164U, 158U, 62U, 84U, 197U, 234U, 84U, 201U, 139U, 149U, 222U, 129U, 188U, 200U, 7U };

static uint8_t
vectors_low48[32U] =
  {
    180U, 226U, 66U, 110U, 152U, 246U, 238U, 217U, 122U, 108U, 223U, 105U, 10U, 137U, 238U, 16U,
    158U, 132U, 195U, 220U, 161U, 108U, 136U, 60U, 38U, 250U, 74U, 198U, 113U, 99U, 141U, 141U
  };

static uint8_t
vectors_low49[32U] =
  {
    91U, 209U, 224U, 134U, 237U, 34U, 140U, 253U, 139U, 85U, 193U, 115U, 31U, 234U, 64U, 195U, 166U,
    61U, 2U, 37U, 153U, 202U, 45U, 164U, 187U, 35U, 17U, 143U, 72U, 33U, 186U, 98U
  };

static uint8_t
vectors_low50[32U] =
  {
    183U, 84U, 181U, 58U, 194U, 38U, 232U, 235U, 228U, 122U, 61U, 49U, 73U, 110U, 200U, 34U, 222U,
    6U, 252U, 162U, 231U, 239U, 91U, 241U, 222U, 198U, 200U, 61U, 5U, 54U, 142U, 195U
  };

static uint8_t
vectors_low51[32U] =
  {
    250U, 126U, 118U, 178U, 128U, 93U, 144U, 179U, 216U, 159U, 255U, 84U, 80U, 16U, 216U, 79U, 103U,
    170U, 58U, 44U, 158U, 178U, 186U, 35U, 46U, 117U, 244U, 213U, 50U, 103U, 218U, 195U
  };

static uint8_t
vectors_low52[128U] =
  {
    223U, 107U, 36U, 96U, 104U, 143U, 165U, 55U, 223U, 61U, 223U, 229U, 87U, 95U, 202U, 94U, 184U,
    171U, 173U, 86U, 203U, 196U, 229U, 166U, 24U, 162U, 180U, 167U, 218U, 246U, 226U, 21U, 195U,
    164U, 151U, 151U, 76U, 80U, 47U, 157U, 14U, 195U, 93U, 227U, 252U, 46U, 165U, 212U, 241U, 13U,
    233U, 178U, 174U, 230U, 109U, 204U, 126U, 122U, 230U, 53U, 121U, 131U, 9U, 89U, 89U, 184U, 23U,
    240U, 56U, 62U, 48U, 48U, 119U, 27U, 210U, 237U, 151U, 64U, 106U, 207U, 120U, 161U, 164U, 165U,
    243U, 15U, 160U, 153U, 34U, 137U, 201U, 32U, 46U, 105U, 227U, 235U, 30U, 171U, 226U, 39U, 193U,
    20U, 9U, 255U, 67U, 15U, 109U, 252U, 161U, 169U, 35U, 168U, 177U, 123U, 196U, 184U, 126U, 144U,
    128U, 7U, 245U, 233U, 117U, 156U, 65U, 72U, 43U, 1U
  };

static uint8_t
vectors_low53[32U] =
  {
    104U, 242U, 29U, 20U, 82U, 93U, 86U, 35U, 60U, 126U, 38U, 52U, 130U, 211U, 68U, 195U, 136U,
    168U, 64U, 16U, 58U, 119U, 251U, 32U, 172U, 96U, 206U, 70U, 60U, 171U, 220U, 121U
  };

static uint8_t
vectors_low54[16U] =
  { 89U, 250U, 128U, 174U, 87U, 15U, 62U, 12U, 96U, 172U, 126U, 37U, 120U, 206U, 195U, 203U };

static uint8_t
vectors_low55[32U] =
  {
    117U, 132U, 180U, 22U, 101U, 48U, 68U, 47U, 6U, 226U, 65U, 221U, 144U, 79U, 86U, 33U, 103U,
    226U, 253U, 174U, 50U, 71U, 171U, 133U, 58U, 74U, 157U, 72U, 132U, 165U, 250U, 70U
  };

static uint8_t
vectors_low56[32U] =
  {
    246U, 165U, 72U, 47U, 19U, 144U, 69U, 197U, 56U, 156U, 146U, 70U, 215U, 114U, 199U, 130U, 196U,
    235U, 247U, 156U, 58U, 132U, 181U, 207U, 119U, 159U, 69U, 138U, 105U, 165U, 41U, 20U
  };

static uint8_t
vectors_low57[32U] =
  {
    157U, 55U, 177U, 206U, 153U, 248U, 7U, 153U, 147U, 221U, 240U, 189U, 84U, 186U, 178U, 24U, 1U,
    102U, 133U, 178U, 38U, 85U, 166U, 120U, 206U, 67U, 0U, 16U, 95U, 58U, 69U, 183U
  };

static uint8_t
vectors_low58[32U] =
  {
    76U, 151U, 198U, 112U, 38U, 255U, 67U, 194U, 238U, 115U, 14U, 123U, 44U, 232U, 204U, 228U, 121U,
    79U, 208U, 88U, 141U, 235U, 22U, 24U, 95U, 166U, 121U, 45U, 221U, 13U, 70U, 222U
  };

static uint8_t
vectors_low59[128U] =
  {
    229U, 248U, 135U, 75U, 224U, 168U, 52U, 90U, 171U, 242U, 248U, 41U, 167U, 192U, 107U, 180U, 14U,
    96U, 134U, 149U, 8U, 194U, 189U, 239U, 7U, 29U, 115U, 105U, 44U, 2U, 101U, 246U, 165U, 191U,
    156U, 166U, 207U, 71U, 215U, 92U, 189U, 157U, 248U, 139U, 156U, 178U, 54U, 205U, 252U, 227U,
    125U, 47U, 212U, 145U, 63U, 23U, 125U, 189U, 65U, 136U, 125U, 174U, 17U, 110U, 223U, 189U, 173U,
    79U, 214U, 228U, 193U, 165U, 26U, 173U, 159U, 157U, 106U, 254U, 127U, 202U, 252U, 237U, 69U,
    164U, 145U, 61U, 116U, 42U, 126U, 192U, 15U, 214U, 23U, 13U, 99U, 166U, 143U, 152U, 109U, 140U,
    35U, 87U, 118U, 94U, 77U, 56U, 131U, 93U, 63U, 234U, 48U, 26U, 250U, 180U, 58U, 80U, 189U, 158U,
    221U, 45U, 236U, 106U, 151U, 151U, 50U, 178U, 82U, 146U
  };

static uint8_t
vectors_low60[32U] =
  {
    26U, 225U, 42U, 94U, 78U, 154U, 74U, 91U, 250U, 121U, 218U, 48U, 169U, 230U, 198U, 47U, 252U,
    99U, 149U, 114U, 239U, 18U, 84U, 25U, 77U, 18U, 154U, 22U, 235U, 83U, 199U, 22U
  };

static uint8_t
vectors_low61[16U] =
  { 83U, 153U, 179U, 72U, 31U, 223U, 36U, 211U, 115U, 34U, 34U, 103U, 121U, 10U, 15U, 236U };

static uint8_t
vectors_low62[32U] =
  {
    130U, 128U, 207U, 220U, 215U, 165U, 117U, 129U, 110U, 1U, 153U, 225U, 21U, 218U, 14U, 167U,
    124U, 174U, 157U, 48U, 180U, 156U, 137U, 26U, 108U, 34U, 94U, 144U, 55U, 186U, 103U, 226U
  };

static uint8_t
vectors_low63[32U] =
  {
    104U, 21U, 84U, 255U, 112U, 38U, 88U, 18U, 46U, 145U, 186U, 1U, 116U, 80U, 207U, 223U, 200U,
    227U, 244U, 145U, 17U, 83U, 247U, 188U, 196U, 40U, 64U, 62U, 156U, 123U, 157U, 104U
  };

static uint8_t
vectors_low64[32U] =
  {
    34U, 103U, 50U, 183U, 164U, 87U, 207U, 10U, 192U, 239U, 9U, 253U, 79U, 129U, 41U, 101U, 115U,
    180U, 154U, 104U, 222U, 94U, 122U, 195U, 7U, 14U, 20U, 140U, 149U, 232U, 227U, 35U
  };

static uint8_t
vectors_low65[32U] =
  {
    69U, 148U, 43U, 94U, 154U, 26U, 18U, 142U, 133U, 225U, 44U, 52U, 89U, 99U, 116U, 221U, 200U,
    95U, 215U, 80U, 46U, 86U, 51U, 199U, 57U, 15U, 198U, 230U, 241U, 229U, 239U, 86U
  };

static uint8_t
vectors_low66[32U] =
  {
    111U, 197U, 153U, 41U, 180U, 30U, 119U, 7U, 40U, 134U, 175U, 244U, 95U, 115U, 123U, 68U, 155U,
    16U, 94U, 215U, 234U, 203U, 215U, 76U, 124U, 191U, 237U, 245U, 51U, 219U, 234U, 161U
  };

static uint8_t
vectors_low67[128U] =
  {
    183U, 84U, 115U, 50U, 225U, 80U, 150U, 99U, 252U, 254U, 162U, 18U, 143U, 127U, 58U, 61U, 244U,
    132U, 205U, 141U, 240U, 52U, 176U, 1U, 153U, 21U, 125U, 53U, 214U, 30U, 53U, 241U, 169U, 212U,
    129U, 199U, 210U, 232U, 19U, 5U, 97U, 109U, 112U, 252U, 55U, 30U, 228U, 89U, 176U, 178U, 38U,
    125U, 98U, 126U, 146U, 133U, 144U, 237U, 202U, 195U, 35U, 24U, 152U, 178U, 78U, 243U, 120U,
    170U, 156U, 61U, 56U, 22U, 25U, 246U, 101U, 55U, 155U, 231U, 108U, 124U, 27U, 213U, 53U, 80U,
    92U, 86U, 61U, 179U, 114U, 95U, 3U, 71U, 134U, 227U, 91U, 221U, 144U, 66U, 147U, 5U, 253U, 113U,
    215U, 191U, 104U, 14U, 140U, 221U, 109U, 76U, 52U, 141U, 151U, 7U, 143U, 92U, 245U, 232U, 157U,
    238U, 45U, 196U, 16U, 250U, 212U, 242U, 163U, 15U
  };

static uint8_t
vectors_low68[32U] =
  {
    16U, 184U, 120U, 156U, 219U, 214U, 119U, 132U, 66U, 164U, 94U, 223U, 34U, 139U, 153U, 35U, 244U,
    82U, 99U, 26U, 208U, 254U, 158U, 96U, 141U, 16U, 130U, 107U, 167U, 29U, 167U, 202U
  };

static uint8_t
vectors_low69[16U] =
  { 21U, 159U, 197U, 216U, 229U, 14U, 181U, 110U, 34U, 151U, 71U, 137U, 177U, 220U, 32U, 209U };

static uint8_t
vectors_low70[32U] =
  {
    45U, 213U, 158U, 55U, 118U, 108U, 102U, 117U, 113U, 183U, 121U, 192U, 110U, 18U, 186U, 33U,
    145U, 136U, 72U, 151U, 114U, 244U, 134U, 49U, 166U, 114U, 139U, 91U, 134U, 126U, 60U, 244U
  };

static uint8_t
vectors_low71[32U] =
  {
    150U, 109U, 148U, 32U, 56U, 3U, 5U, 9U, 178U, 14U, 97U, 0U, 98U, 4U, 43U, 107U, 241U, 4U, 129U,
    40U, 24U, 137U, 50U, 146U, 166U, 141U, 87U, 209U, 206U, 134U, 81U, 81U
  };

static uint8_t
vectors_low72[128U] =
  {
    62U, 106U, 205U, 139U, 78U, 133U, 180U, 160U, 247U, 146U, 143U, 107U, 212U, 26U, 142U, 107U,
    82U, 82U, 79U, 231U, 39U, 35U, 160U, 80U, 150U, 55U, 211U, 63U, 21U, 175U, 231U, 216U, 218U,
    106U, 21U, 32U, 155U, 158U, 65U, 73U, 87U, 111U, 187U, 31U, 216U, 49U, 247U, 132U, 192U, 68U,
    57U, 171U, 218U, 70U, 5U, 208U, 101U, 86U, 220U, 48U, 2U, 5U, 91U, 88U, 85U, 251U, 162U, 1U,
    246U, 218U, 239U, 121U, 247U, 141U, 0U, 30U, 214U, 158U, 202U, 138U, 65U, 133U, 19U, 208U, 36U,
    100U, 232U, 215U, 66U, 194U, 121U, 156U, 214U, 142U, 223U, 190U, 136U, 174U, 155U, 53U, 160U,
    170U, 6U, 92U, 66U, 164U, 119U, 0U, 88U, 196U, 176U, 38U, 208U, 53U, 10U, 122U, 250U, 156U, 82U,
    195U, 199U, 250U, 5U, 79U, 138U, 150U, 216U, 135U
  };

static uint8_t
vectors_low73[32U] =
  {
    229U, 250U, 115U, 190U, 217U, 147U, 64U, 201U, 26U, 177U, 125U, 3U, 158U, 253U, 36U, 143U, 205U,
    26U, 184U, 176U, 160U, 246U, 85U, 221U, 49U, 73U, 148U, 150U, 133U, 236U, 173U, 189U
  };

static uint8_t
vectors_low74[16U] =
  { 175U, 75U, 148U, 240U, 131U, 0U, 161U, 235U, 5U, 154U, 214U, 166U, 135U, 162U, 47U, 209U };

static uint8_t
vectors_low75[32U] =
  {
    208U, 9U, 90U, 79U, 215U, 246U, 214U, 222U, 42U, 31U, 11U, 41U, 44U, 71U, 236U, 232U, 86U, 91U,
    248U, 194U, 2U, 240U, 114U, 61U, 13U, 231U, 242U, 247U, 144U, 69U, 55U, 191U
  };

static uint8_t
vectors_low76[32U] =
  {
    77U, 216U, 31U, 173U, 83U, 74U, 163U, 110U, 23U, 77U, 6U, 102U, 110U, 149U, 164U, 217U, 179U,
    98U, 43U, 246U, 13U, 138U, 86U, 44U, 118U, 69U, 65U, 234U, 124U, 151U, 79U, 233U
  };

static uint8_t
vectors_low77[32U] =
  {
    17U, 124U, 160U, 170U, 157U, 87U, 151U, 48U, 5U, 250U, 209U, 248U, 160U, 47U, 45U, 98U, 172U,
    112U, 23U, 88U, 85U, 107U, 66U, 168U, 213U, 56U, 46U, 229U, 85U, 64U, 168U, 107U
  };

static uint8_t
vectors_low78[32U] =
  {
    163U, 107U, 164U, 30U, 9U, 90U, 64U, 243U, 121U, 133U, 165U, 205U, 115U, 21U, 243U, 119U, 49U,
    50U, 244U, 145U, 239U, 138U, 69U, 61U, 57U, 112U, 174U, 114U, 244U, 28U, 83U, 101U
  };

static uint8_t
vectors_low79[32U] =
  {
    171U, 186U, 29U, 22U, 37U, 86U, 234U, 171U, 114U, 146U, 82U, 205U, 72U, 222U, 173U, 45U, 125U,
    80U, 166U, 56U, 91U, 29U, 39U, 5U, 145U, 212U, 101U, 250U, 56U, 197U, 89U, 125U
  };

static uint8_t
vectors_low80[128U] =
  {
    43U, 239U, 1U, 190U, 161U, 251U, 10U, 181U, 252U, 203U, 180U, 116U, 161U, 186U, 203U, 54U, 31U,
    252U, 195U, 38U, 241U, 217U, 241U, 150U, 144U, 72U, 195U, 146U, 242U, 118U, 30U, 208U, 163U,
    113U, 38U, 67U, 51U, 17U, 222U, 201U, 219U, 24U, 89U, 100U, 72U, 203U, 129U, 78U, 218U, 21U,
    27U, 38U, 78U, 60U, 164U, 100U, 178U, 93U, 228U, 1U, 176U, 227U, 139U, 67U, 233U, 60U, 100U,
    246U, 117U, 243U, 122U, 217U, 30U, 149U, 194U, 78U, 105U, 151U, 220U, 64U, 50U, 250U, 98U, 186U,
    0U, 243U, 200U, 167U, 146U, 214U, 181U, 57U, 164U, 232U, 41U, 11U, 16U, 23U, 59U, 107U, 53U,
    247U, 39U, 143U, 52U, 244U, 13U, 247U, 196U, 207U, 38U, 81U, 131U, 80U, 223U, 167U, 226U, 67U,
    98U, 50U, 12U, 132U, 70U, 150U, 58U, 154U, 19U, 105U
  };

static uint8_t
vectors_low81[32U] =
  {
    12U, 44U, 36U, 40U, 127U, 38U, 76U, 29U, 83U, 41U, 209U, 137U, 137U, 231U, 249U, 206U, 6U, 184U,
    169U, 68U, 109U, 38U, 205U, 144U, 237U, 113U, 135U, 146U, 177U, 61U, 173U, 148U
  };

static uint8_t
vectors_low82[16U] =
  { 253U, 1U, 208U, 56U, 56U, 107U, 55U, 112U, 159U, 141U, 160U, 53U, 121U, 248U, 43U, 204U };

static uint8_t
vectors_low83[32U] =
  {
    5U, 181U, 35U, 204U, 248U, 128U, 191U, 176U, 218U, 131U, 160U, 94U, 78U, 178U, 234U, 40U, 204U,
    117U, 161U, 228U, 249U, 224U, 156U, 138U, 57U, 89U, 177U, 134U, 34U, 69U, 59U, 220U
  };

static uint8_t
vectors_low84[32U] =
  {
    133U, 224U, 106U, 140U, 163U, 167U, 65U, 130U, 28U, 58U, 42U, 136U, 24U, 19U, 22U, 117U, 19U,
    110U, 253U, 88U, 65U, 203U, 150U, 231U, 221U, 236U, 121U, 67U, 204U, 22U, 159U, 163U
  };

static uint8_t
vectors_low85[32U] =
  {
    107U, 132U, 46U, 28U, 253U, 204U, 98U, 3U, 250U, 55U, 80U, 207U, 179U, 199U, 34U, 247U, 168U,
    80U, 20U, 192U, 110U, 120U, 218U, 142U, 166U, 31U, 15U, 158U, 124U, 32U, 203U, 74U
  };

static uint8_t
vectors_low86[32U] =
  {
    123U, 164U, 161U, 73U, 74U, 11U, 73U, 131U, 136U, 249U, 77U, 23U, 38U, 184U, 186U, 246U, 62U,
    68U, 160U, 60U, 43U, 251U, 191U, 243U, 90U, 208U, 57U, 179U, 152U, 129U, 114U, 10U
  };

static uint8_t
vectors_low87[128U] =
  {
    177U, 0U, 30U, 120U, 253U, 178U, 109U, 201U, 46U, 35U, 137U, 236U, 14U, 181U, 235U, 48U, 89U,
    244U, 74U, 180U, 242U, 234U, 214U, 199U, 74U, 118U, 21U, 171U, 134U, 135U, 56U, 24U, 152U, 245U,
    176U, 216U, 56U, 36U, 127U, 65U, 120U, 107U, 184U, 60U, 7U, 119U, 19U, 255U, 132U, 84U, 14U,
    213U, 64U, 97U, 244U, 208U, 2U, 100U, 105U, 157U, 244U, 118U, 135U, 60U, 13U, 208U, 195U, 99U,
    185U, 152U, 5U, 78U, 220U, 100U, 8U, 78U, 254U, 237U, 125U, 207U, 40U, 215U, 113U, 153U, 121U,
    151U, 132U, 72U, 215U, 220U, 232U, 248U, 170U, 56U, 104U, 229U, 107U, 137U, 238U, 191U, 39U,
    95U, 0U, 10U, 57U, 196U, 207U, 181U, 175U, 22U, 166U, 67U, 2U, 169U, 9U, 134U, 204U, 48U, 66U,
    216U, 130U, 111U, 46U, 63U, 127U, 219U, 133U, 157U
  };

static uint8_t
vectors_low88[32U] =
  {
    193U, 61U, 108U, 214U, 59U, 183U, 147U, 17U, 116U, 105U, 111U, 62U, 4U, 160U, 196U, 28U, 176U,
    178U, 86U, 17U, 52U, 232U, 71U, 206U, 3U, 227U, 99U, 38U, 184U, 3U, 248U, 171U
  };

static uint8_t
vectors_low89[16U] =
  { 32U, 132U, 171U, 50U, 55U, 67U, 146U, 234U, 159U, 110U, 138U, 71U, 79U, 24U, 233U, 215U };

static uint8_t
vectors_low90[32U] =
  {
    174U, 197U, 166U, 167U, 35U, 42U, 82U, 184U, 28U, 231U, 233U, 129U, 163U, 89U, 206U, 241U, 187U,
    210U, 241U, 239U, 248U, 72U, 131U, 113U, 70U, 140U, 209U, 244U, 20U, 122U, 137U, 194U
  };

static uint8_t
vectors_low91[128U] =
  {
    218U, 234U, 120U, 136U, 23U, 55U, 203U, 38U, 214U, 12U, 54U, 206U, 185U, 254U, 195U, 210U, 129U,
    199U, 174U, 197U, 75U, 75U, 152U, 80U, 147U, 123U, 55U, 59U, 43U, 38U, 33U, 254U, 7U, 117U,
    133U, 161U, 254U, 136U, 38U, 93U, 132U, 242U, 37U, 85U, 46U, 92U, 133U, 203U, 236U, 141U, 0U,
    6U, 150U, 72U, 6U, 90U, 193U, 32U, 115U, 174U, 220U, 232U, 201U, 64U, 70U, 9U, 73U, 181U, 151U,
    102U, 126U, 207U, 206U, 218U, 189U, 122U, 134U, 169U, 121U, 185U, 4U, 162U, 77U, 50U, 219U, 16U,
    34U, 62U, 174U, 90U, 152U, 160U, 209U, 182U, 87U, 27U, 134U, 67U, 223U, 44U, 98U, 101U, 165U,
    214U, 108U, 238U, 159U, 74U, 191U, 197U, 119U, 129U, 70U, 214U, 251U, 43U, 133U, 61U, 130U, 99U,
    108U, 19U, 37U, 178U, 209U, 239U, 69U, 118U
  };

static uint8_t
vectors_low92[32U] =
  {
    136U, 167U, 108U, 22U, 211U, 39U, 14U, 211U, 252U, 209U, 118U, 249U, 215U, 147U, 250U, 12U, 53U,
    81U, 101U, 116U, 193U, 206U, 244U, 37U, 182U, 0U, 118U, 40U, 175U, 163U, 94U, 43U
  };

static uint8_t
vectors_low93[16U] =
  { 255U, 22U, 207U, 124U, 184U, 228U, 157U, 72U, 44U, 253U, 57U, 148U, 171U, 197U, 239U, 138U };

static uint8_t
vectors_low94[32U] =
  {
    146U, 19U, 197U, 78U, 61U, 0U, 45U, 248U, 116U, 17U, 99U, 171U, 157U, 126U, 7U, 87U, 205U, 81U,
    44U, 105U, 26U, 214U, 75U, 175U, 239U, 149U, 203U, 114U, 83U, 155U, 10U, 198U
  };

static uint8_t
vectors_low95[32U] =
  {
    73U, 59U, 100U, 127U, 240U, 179U, 250U, 162U, 146U, 31U, 18U, 248U, 245U, 123U, 145U, 147U, 41U,
    242U, 175U, 47U, 193U, 241U, 69U, 118U, 217U, 223U, 47U, 140U, 194U, 173U, 167U, 166U
  };

static uint8_t
vectors_low96[128U] =
  {
    241U, 51U, 10U, 133U, 249U, 0U, 55U, 135U, 107U, 55U, 73U, 32U, 62U, 132U, 146U, 135U, 68U, 74U,
    130U, 127U, 10U, 88U, 194U, 73U, 255U, 134U, 143U, 193U, 173U, 186U, 77U, 206U, 40U, 94U, 7U,
    106U, 31U, 138U, 225U, 218U, 140U, 249U, 254U, 20U, 147U, 30U, 129U, 100U, 24U, 108U, 151U,
    168U, 254U, 175U, 36U, 88U, 52U, 81U, 241U, 22U, 230U, 95U, 142U, 67U, 46U, 126U, 213U, 90U,
    54U, 104U, 49U, 32U, 55U, 126U, 35U, 18U, 141U, 202U, 21U, 64U, 254U, 251U, 243U, 175U, 27U,
    86U, 213U, 199U, 65U, 135U, 245U, 40U, 109U, 10U, 149U, 251U, 85U, 147U, 23U, 112U, 84U, 48U,
    96U, 206U, 141U, 240U, 143U, 60U, 25U, 89U, 161U, 244U, 252U, 54U, 182U, 70U, 113U, 224U, 101U,
    79U, 255U, 231U, 13U, 150U, 213U, 33U, 190U, 33U
  };

static uint8_t
vectors_low97[32U] =
  {
    232U, 233U, 159U, 252U, 240U, 138U, 173U, 142U, 80U, 56U, 111U, 93U, 7U, 157U, 121U, 211U, 219U,
    120U, 58U, 116U, 22U, 92U, 97U, 38U, 180U, 43U, 49U, 64U, 247U, 68U, 167U, 199U
  };

static uint8_t
vectors_low98[16U] =
  { 35U, 84U, 25U, 48U, 200U, 199U, 114U, 173U, 182U, 41U, 129U, 219U, 239U, 141U, 5U, 78U };

static uint8_t
vectors_low99[32U] =
  {
    205U, 207U, 28U, 48U, 34U, 137U, 4U, 189U, 123U, 163U, 23U, 152U, 191U, 187U, 214U, 71U, 87U,
    170U, 37U, 26U, 201U, 161U, 174U, 140U, 32U, 160U, 80U, 103U, 15U, 234U, 197U, 155U
  };

static uint8_t
vectors_low100[32U] =
  {
    84U, 110U, 4U, 36U, 125U, 108U, 181U, 33U, 42U, 87U, 182U, 47U, 153U, 225U, 204U, 167U, 103U,
    165U, 118U, 140U, 247U, 146U, 150U, 244U, 95U, 13U, 178U, 71U, 50U, 186U, 99U, 104U
  };

static uint8_t
vectors_low101[32U] =
  {
    253U, 69U, 246U, 108U, 141U, 237U, 228U, 19U, 135U, 55U, 60U, 56U, 103U, 70U, 5U, 243U, 224U,
    117U, 201U, 183U, 207U, 198U, 97U, 35U, 165U, 71U, 139U, 143U, 142U, 58U, 178U, 118U
  };

static uint8_t
vectors_low102[32U] =
  {
    57U, 145U, 26U, 121U, 198U, 237U, 187U, 200U, 5U, 165U, 13U, 42U, 160U, 24U, 116U, 32U, 148U,
    23U, 122U, 142U, 33U, 109U, 100U, 124U, 100U, 66U, 140U, 0U, 22U, 154U, 178U, 214U
  };

static uint8_t
vectors_low103[192U] =
  {
    135U, 21U, 119U, 221U, 243U, 75U, 41U, 229U, 202U, 241U, 50U, 170U, 130U, 225U, 210U, 241U, 88U,
    107U, 118U, 227U, 154U, 171U, 98U, 172U, 208U, 47U, 109U, 68U, 64U, 144U, 138U, 119U, 42U, 197U,
    246U, 253U, 72U, 197U, 245U, 95U, 30U, 190U, 14U, 118U, 34U, 26U, 196U, 107U, 131U, 74U, 138U,
    79U, 93U, 217U, 149U, 135U, 33U, 238U, 5U, 59U, 163U, 174U, 241U, 87U, 78U, 189U, 152U, 10U,
    93U, 166U, 169U, 70U, 147U, 102U, 39U, 23U, 238U, 84U, 138U, 240U, 249U, 33U, 66U, 29U, 26U,
    251U, 129U, 78U, 77U, 23U, 153U, 211U, 81U, 136U, 157U, 42U, 27U, 221U, 87U, 87U, 10U, 145U,
    62U, 66U, 142U, 102U, 19U, 177U, 110U, 21U, 140U, 28U, 254U, 208U, 56U, 246U, 87U, 137U, 32U,
    214U, 13U, 183U, 61U, 193U, 10U, 64U, 218U, 155U, 195U, 99U, 160U, 32U, 107U, 78U, 126U, 73U,
    103U, 14U, 204U, 234U, 134U, 110U, 253U, 154U, 5U, 188U, 35U, 112U, 66U, 207U, 5U, 47U, 42U,
    65U, 64U, 249U, 55U, 126U, 60U, 103U, 146U, 184U, 142U, 160U, 99U, 35U, 252U, 235U, 185U, 156U,
    100U, 63U, 193U, 195U, 101U, 55U, 88U, 214U, 134U, 108U, 219U, 20U, 136U, 55U, 251U, 15U, 223U,
    119U, 222U, 21U, 100U, 207U
  };

static uint8_t
vectors_low104[32U] =
  {
    147U, 25U, 20U, 143U, 183U, 194U, 56U, 151U, 147U, 233U, 245U, 60U, 211U, 180U, 173U, 143U, 27U,
    183U, 87U, 16U, 8U, 143U, 28U, 154U, 24U, 67U, 76U, 225U, 59U, 25U, 13U, 162U
  };

static uint8_t
vectors_low105[16U] =
  { 17U, 253U, 197U, 60U, 19U, 174U, 163U, 57U, 133U, 186U, 38U, 120U, 232U, 216U, 109U, 9U };

static uint8_t
vectors_low106[32U] =
  {
    134U, 25U, 41U, 14U, 151U, 95U, 28U, 80U, 246U, 96U, 108U, 112U, 39U, 239U, 233U, 200U, 67U,
    141U, 50U, 9U, 219U, 113U, 237U, 208U, 35U, 175U, 14U, 176U, 36U, 162U, 130U, 210U
  };

static uint8_t
vectors_low107[192U] =
  {
    48U, 194U, 50U, 126U, 221U, 181U, 195U, 148U, 45U, 144U, 0U, 110U, 173U, 204U, 252U, 38U, 210U,
    123U, 20U, 159U, 25U, 83U, 137U, 171U, 186U, 80U, 124U, 7U, 70U, 228U, 29U, 127U, 184U, 207U,
    48U, 193U, 95U, 44U, 223U, 247U, 63U, 243U, 215U, 123U, 76U, 160U, 210U, 137U, 240U, 102U, 0U,
    115U, 242U, 199U, 63U, 131U, 206U, 129U, 154U, 106U, 125U, 143U, 233U, 17U, 253U, 16U, 151U,
    120U, 181U, 1U, 53U, 126U, 202U, 115U, 7U, 157U, 134U, 190U, 208U, 145U, 109U, 238U, 222U, 84U,
    226U, 232U, 110U, 202U, 44U, 4U, 243U, 208U, 112U, 110U, 42U, 85U, 255U, 132U, 148U, 44U, 191U,
    238U, 34U, 181U, 169U, 45U, 48U, 155U, 132U, 184U, 221U, 61U, 236U, 185U, 243U, 242U, 196U,
    178U, 78U, 251U, 79U, 56U, 40U, 51U, 255U, 184U, 103U, 181U, 254U, 5U, 75U, 33U, 212U, 125U,
    182U, 197U, 47U, 245U, 47U, 170U, 19U, 206U, 42U, 189U, 247U, 153U, 110U, 35U, 168U, 201U, 107U,
    172U, 72U, 192U, 41U, 128U, 217U, 98U, 52U, 228U, 120U, 55U, 0U, 39U, 213U, 91U, 168U, 117U,
    44U, 23U, 199U, 161U, 191U, 98U, 83U, 8U, 70U, 84U, 231U, 156U, 19U, 186U, 204U, 81U, 193U,
    129U, 92U, 139U, 100U, 126U, 54U, 203U
  };

static uint8_t
vectors_low108[32U] =
  {
    249U, 226U, 80U, 96U, 103U, 94U, 76U, 87U, 52U, 216U, 24U, 217U, 195U, 26U, 11U, 35U, 36U, 116U,
    82U, 5U, 119U, 228U, 47U, 140U, 83U, 248U, 3U, 174U, 226U, 52U, 159U, 74U
  };

static uint8_t
vectors_low109[16U] =
  { 154U, 98U, 164U, 28U, 243U, 245U, 169U, 225U, 152U, 223U, 248U, 201U, 7U, 163U, 90U, 63U };

static uint8_t
vectors_low110[32U] =
  {
    136U, 138U, 117U, 41U, 144U, 154U, 227U, 96U, 83U, 199U, 91U, 173U, 180U, 77U, 16U, 49U, 24U,
    225U, 113U, 120U, 74U, 123U, 103U, 220U, 13U, 122U, 78U, 27U, 29U, 68U, 57U, 26U
  };

static uint8_t
vectors_low111[32U] =
  {
    16U, 162U, 93U, 0U, 39U, 177U, 197U, 95U, 97U, 93U, 59U, 124U, 63U, 35U, 93U, 121U, 26U, 129U,
    223U, 232U, 33U, 83U, 21U, 224U, 195U, 143U, 204U, 222U, 39U, 165U, 216U, 218U
  };

static uint8_t
vectors_low112[32U] =
  {
    123U, 16U, 226U, 80U, 68U, 171U, 208U, 145U, 116U, 144U, 231U, 241U, 168U, 207U, 210U, 73U,
    102U, 128U, 63U, 201U, 190U, 38U, 15U, 58U, 181U, 191U, 149U, 70U, 147U, 246U, 8U, 133U
  };

static uint8_t
vectors_low113[32U] =
  {
    163U, 86U, 62U, 197U, 192U, 137U, 255U, 241U, 39U, 178U, 162U, 234U, 239U, 18U, 189U, 12U, 179U,
    177U, 143U, 58U, 9U, 153U, 117U, 70U, 102U, 17U, 58U, 5U, 47U, 212U, 67U, 249U
  };

static uint8_t
vectors_low114[192U] =
  {
    131U, 185U, 254U, 244U, 243U, 28U, 113U, 174U, 191U, 55U, 83U, 208U, 64U, 66U, 8U, 103U, 137U,
    135U, 252U, 76U, 178U, 210U, 147U, 168U, 172U, 138U, 84U, 122U, 237U, 24U, 167U, 169U, 224U,
    157U, 129U, 150U, 160U, 125U, 110U, 151U, 201U, 9U, 230U, 74U, 239U, 0U, 217U, 185U, 83U, 12U,
    161U, 205U, 105U, 214U, 88U, 7U, 133U, 125U, 155U, 48U, 167U, 73U, 36U, 166U, 190U, 150U, 221U,
    150U, 252U, 72U, 173U, 89U, 49U, 137U, 39U, 54U, 167U, 127U, 98U, 246U, 140U, 63U, 202U, 117U,
    175U, 62U, 46U, 165U, 178U, 163U, 54U, 241U, 224U, 128U, 162U, 79U, 162U, 143U, 129U, 253U,
    139U, 26U, 52U, 211U, 200U, 170U, 198U, 80U, 172U, 170U, 210U, 94U, 209U, 224U, 11U, 196U, 64U,
    146U, 161U, 57U, 64U, 200U, 33U, 148U, 42U, 221U, 24U, 191U, 14U, 215U, 12U, 87U, 140U, 48U,
    87U, 17U, 176U, 164U, 153U, 30U, 197U, 189U, 223U, 174U, 206U, 232U, 4U, 97U, 155U, 25U, 127U,
    215U, 22U, 170U, 46U, 103U, 19U, 192U, 207U, 145U, 234U, 10U, 109U, 70U, 164U, 208U, 234U, 128U,
    167U, 247U, 15U, 79U, 199U, 83U, 7U, 211U, 66U, 230U, 157U, 31U, 223U, 249U, 137U, 128U, 139U,
    117U, 0U, 39U, 92U, 208U, 82U, 24U
  };

static uint8_t
vectors_low115[32U] =
  {
    88U, 235U, 206U, 196U, 83U, 159U, 74U, 241U, 179U, 42U, 133U, 65U, 129U, 221U, 15U, 81U, 43U,
    140U, 112U, 79U, 164U, 117U, 55U, 9U, 106U, 118U, 158U, 255U, 40U, 197U, 145U, 101U
  };

static uint8_t
vectors_low116[16U] =
  { 161U, 130U, 38U, 207U, 199U, 121U, 239U, 201U, 85U, 15U, 123U, 224U, 32U, 6U, 216U, 60U };

static uint8_t
vectors_low117[32U] =
  {
    35U, 12U, 214U, 230U, 144U, 158U, 48U, 29U, 30U, 153U, 236U, 209U, 255U, 242U, 178U, 205U, 0U,
    165U, 108U, 122U, 104U, 76U, 137U, 7U, 187U, 177U, 60U, 227U, 233U, 160U, 203U, 206U
  };

static uint8_t
vectors_low118[256U] =
  {
    111U, 78U, 134U, 243U, 9U, 246U, 145U, 68U, 96U, 57U, 97U, 197U, 54U, 110U, 79U, 155U, 22U,
    209U, 12U, 16U, 89U, 62U, 166U, 137U, 168U, 231U, 67U, 90U, 50U, 125U, 37U, 36U, 244U, 70U,
    136U, 19U, 234U, 127U, 50U, 72U, 216U, 212U, 187U, 225U, 123U, 23U, 92U, 252U, 64U, 97U, 113U,
    73U, 152U, 57U, 40U, 178U, 103U, 220U, 12U, 77U, 180U, 109U, 44U, 23U, 254U, 139U, 192U, 118U,
    67U, 134U, 117U, 138U, 241U, 168U, 36U, 225U, 46U, 184U, 151U, 254U, 175U, 193U, 199U, 239U,
    102U, 248U, 15U, 252U, 217U, 147U, 170U, 1U, 110U, 19U, 153U, 145U, 205U, 232U, 67U, 94U, 230U,
    187U, 13U, 228U, 90U, 127U, 182U, 30U, 177U, 166U, 190U, 183U, 110U, 1U, 43U, 132U, 142U, 160U,
    3U, 246U, 135U, 83U, 126U, 75U, 208U, 12U, 237U, 55U, 239U, 221U, 166U, 99U, 51U, 181U, 58U,
    141U, 213U, 34U, 12U, 40U, 31U, 191U, 104U, 191U, 217U, 231U, 34U, 133U, 231U, 129U, 151U, 136U,
    30U, 252U, 84U, 13U, 164U, 193U, 186U, 128U, 162U, 38U, 1U, 58U, 45U, 112U, 152U, 211U, 74U,
    244U, 17U, 46U, 123U, 140U, 134U, 90U, 241U, 84U, 9U, 246U, 144U, 27U, 149U, 47U, 238U, 74U,
    71U, 78U, 64U, 39U, 5U, 30U, 29U, 206U, 135U, 157U, 223U, 94U, 132U, 243U, 148U, 125U, 201U,
    185U, 65U, 25U, 214U, 126U, 107U, 72U, 237U, 111U, 214U, 177U, 248U, 19U, 193U, 61U, 63U, 243U,
    14U, 18U, 30U, 252U, 231U, 145U, 133U, 51U, 146U, 95U, 80U, 200U, 227U, 129U, 232U, 126U, 166U,
    133U, 249U, 147U, 97U, 155U, 172U, 201U, 239U, 192U, 174U, 188U, 136U, 75U, 69U, 6U, 70U, 238U,
    170U, 94U
  };

static uint8_t
vectors_low119[32U] =
  {
    225U, 210U, 215U, 46U, 121U, 7U, 231U, 33U, 76U, 178U, 102U, 241U, 239U, 100U, 19U, 149U, 229U,
    75U, 57U, 232U, 54U, 83U, 4U, 102U, 27U, 11U, 238U, 55U, 31U, 50U, 70U, 82U
  };

static uint8_t
vectors_low120[16U] =
  { 132U, 23U, 255U, 213U, 132U, 32U, 228U, 142U, 192U, 99U, 222U, 93U, 244U, 70U, 46U, 57U };

static uint8_t
vectors_low121[32U] =
  {
    230U, 202U, 225U, 181U, 243U, 163U, 161U, 47U, 170U, 175U, 57U, 185U, 142U, 229U, 146U, 200U,
    212U, 245U, 107U, 157U, 69U, 52U, 173U, 213U, 16U, 75U, 53U, 125U, 120U, 140U, 35U, 171U
  };

static uint8_t
vectors_low122[256U] =
  {
    98U, 106U, 8U, 99U, 50U, 26U, 199U, 94U, 11U, 98U, 64U, 234U, 106U, 97U, 148U, 88U, 99U, 74U,
    151U, 130U, 69U, 193U, 83U, 56U, 25U, 201U, 113U, 20U, 230U, 57U, 20U, 0U, 156U, 156U, 171U,
    115U, 47U, 19U, 16U, 246U, 15U, 100U, 240U, 51U, 176U, 7U, 41U, 66U, 66U, 40U, 103U, 31U, 51U,
    66U, 80U, 153U, 130U, 10U, 177U, 8U, 65U, 45U, 70U, 15U, 50U, 192U, 1U, 91U, 115U, 152U, 126U,
    147U, 123U, 155U, 189U, 210U, 158U, 91U, 251U, 141U, 187U, 108U, 149U, 210U, 182U, 159U, 204U,
    188U, 38U, 176U, 96U, 207U, 10U, 93U, 192U, 153U, 47U, 176U, 231U, 107U, 56U, 188U, 214U, 79U,
    215U, 167U, 38U, 113U, 78U, 140U, 133U, 66U, 212U, 75U, 47U, 156U, 93U, 47U, 47U, 140U, 179U,
    112U, 185U, 94U, 8U, 107U, 7U, 232U, 143U, 73U, 47U, 81U, 254U, 108U, 40U, 141U, 120U, 183U,
    109U, 12U, 58U, 97U, 70U, 201U, 223U, 206U, 83U, 231U, 108U, 219U, 189U, 21U, 141U, 41U, 68U,
    221U, 16U, 25U, 114U, 71U, 0U, 73U, 84U, 217U, 47U, 107U, 29U, 244U, 186U, 222U, 180U, 187U,
    28U, 152U, 215U, 211U, 218U, 32U, 84U, 227U, 48U, 15U, 109U, 141U, 218U, 136U, 99U, 66U, 46U,
    106U, 4U, 44U, 45U, 132U, 178U, 187U, 237U, 107U, 232U, 143U, 7U, 4U, 118U, 52U, 16U, 119U, 27U,
    55U, 134U, 210U, 246U, 217U, 104U, 182U, 194U, 36U, 224U, 207U, 83U, 94U, 141U, 2U, 193U, 120U,
    178U, 224U, 185U, 14U, 138U, 127U, 202U, 12U, 67U, 27U, 127U, 60U, 244U, 27U, 10U, 124U, 23U,
    119U, 143U, 232U, 194U, 238U, 180U, 66U, 201U, 16U, 186U, 136U, 199U, 195U, 100U, 205U
  };

static uint8_t
vectors_low123[32U] =
  {
    71U, 196U, 45U, 246U, 43U, 77U, 213U, 112U, 239U, 211U, 194U, 114U, 42U, 211U, 154U, 45U, 245U,
    249U, 105U, 161U, 63U, 100U, 95U, 210U, 123U, 82U, 144U, 135U, 123U, 167U, 9U, 22U
  };

static uint8_t
vectors_low124[16U] =
  { 197U, 145U, 147U, 77U, 79U, 102U, 0U, 14U, 191U, 140U, 80U, 143U, 175U, 196U, 79U, 117U };

static uint8_t
vectors_low125[32U] =
  {
    148U, 130U, 41U, 3U, 203U, 92U, 32U, 3U, 195U, 28U, 109U, 7U, 42U, 176U, 221U, 164U, 53U, 173U,
    208U, 222U, 125U, 143U, 157U, 95U, 8U, 181U, 203U, 164U, 16U, 216U, 136U, 253U
  };

static uint8_t
vectors_low126[32U] =
  {
    209U, 106U, 44U, 114U, 198U, 53U, 128U, 185U, 188U, 241U, 86U, 134U, 34U, 20U, 83U, 58U, 71U,
    177U, 104U, 108U, 135U, 26U, 1U, 101U, 96U, 79U, 221U, 0U, 164U, 18U, 164U, 132U
  };

static uint8_t
vectors_low127[256U] =
  {
    247U, 142U, 97U, 180U, 67U, 181U, 169U, 123U, 126U, 73U, 58U, 140U, 227U, 90U, 67U, 84U, 82U,
    144U, 221U, 51U, 209U, 91U, 164U, 191U, 15U, 247U, 143U, 52U, 162U, 92U, 70U, 196U, 255U, 76U,
    212U, 133U, 150U, 76U, 201U, 110U, 144U, 254U, 132U, 125U, 159U, 201U, 228U, 45U, 150U, 228U,
    245U, 170U, 204U, 249U, 118U, 168U, 78U, 62U, 18U, 16U, 12U, 40U, 176U, 247U, 173U, 219U, 28U,
    118U, 248U, 150U, 99U, 225U, 24U, 144U, 240U, 158U, 75U, 238U, 254U, 146U, 138U, 30U, 11U, 48U,
    79U, 29U, 157U, 208U, 65U, 76U, 209U, 21U, 160U, 27U, 100U, 31U, 214U, 156U, 112U, 113U, 242U,
    202U, 124U, 127U, 46U, 83U, 86U, 15U, 78U, 145U, 1U, 11U, 161U, 25U, 72U, 25U, 91U, 197U, 222U,
    181U, 86U, 104U, 111U, 235U, 11U, 185U, 47U, 230U, 27U, 49U, 113U, 230U, 57U, 239U, 71U, 65U,
    143U, 2U, 190U, 55U, 121U, 110U, 253U, 182U, 146U, 9U, 82U, 243U, 168U, 199U, 102U, 181U, 47U,
    204U, 250U, 117U, 126U, 146U, 62U, 56U, 2U, 138U, 132U, 249U, 190U, 27U, 128U, 44U, 31U, 187U,
    187U, 74U, 239U, 130U, 95U, 76U, 94U, 79U, 193U, 191U, 110U, 150U, 243U, 58U, 185U, 14U, 164U,
    134U, 113U, 7U, 24U, 201U, 228U, 243U, 36U, 123U, 42U, 85U, 204U, 239U, 90U, 93U, 52U, 44U,
    172U, 117U, 127U, 11U, 159U, 144U, 188U, 220U, 200U, 194U, 236U, 58U, 67U, 20U, 155U, 189U, 57U,
    36U, 200U, 95U, 11U, 91U, 122U, 228U, 33U, 81U, 244U, 222U, 216U, 38U, 238U, 109U, 71U, 132U,
    158U, 244U, 232U, 175U, 100U, 173U, 246U, 134U, 57U, 130U, 80U, 60U, 35U, 196U, 160U, 81U, 76U,
    224U
  };

static uint8_t
vectors_low128[32U] =
  {
    248U, 64U, 199U, 92U, 224U, 205U, 178U, 0U, 163U, 189U, 152U, 13U, 108U, 237U, 241U, 199U, 50U,
    30U, 95U, 48U, 60U, 208U, 68U, 108U, 122U, 253U, 45U, 45U, 102U, 101U, 116U, 71U
  };

static uint8_t
vectors_low129[16U] =
  { 178U, 21U, 51U, 59U, 21U, 213U, 83U, 38U, 188U, 155U, 235U, 174U, 106U, 227U, 110U, 254U };

static uint8_t
vectors_low130[32U] =
  {
    109U, 92U, 164U, 177U, 237U, 246U, 192U, 175U, 189U, 206U, 2U, 236U, 179U, 9U, 35U, 178U, 244U,
    242U, 179U, 49U, 33U, 226U, 27U, 47U, 254U, 233U, 100U, 204U, 125U, 225U, 171U, 232U
  };

static uint8_t
vectors_low131[32U] =
  {
    163U, 163U, 55U, 198U, 251U, 235U, 106U, 151U, 154U, 71U, 131U, 242U, 183U, 240U, 240U, 221U,
    109U, 58U, 157U, 55U, 71U, 222U, 99U, 154U, 144U, 71U, 36U, 138U, 4U, 161U, 159U, 91U
  };

static uint8_t
vectors_low132[32U] =
  {
    245U, 109U, 43U, 21U, 132U, 186U, 47U, 18U, 156U, 119U, 178U, 149U, 144U, 196U, 225U, 223U,
    218U, 181U, 82U, 123U, 23U, 145U, 227U, 228U, 69U, 117U, 12U, 166U, 212U, 174U, 53U, 66U
  };

static uint8_t
vectors_low133[32U] =
  {
    5U, 189U, 121U, 146U, 73U, 65U, 27U, 55U, 184U, 5U, 144U, 212U, 159U, 51U, 72U, 99U, 27U, 6U,
    162U, 64U, 138U, 97U, 99U, 92U, 112U, 104U, 112U, 3U, 168U, 72U, 83U, 2U
  };

static uint8_t
vectors_low134[32U] =
  {
    18U, 210U, 106U, 195U, 184U, 121U, 36U, 205U, 165U, 215U, 138U, 62U, 60U, 11U, 216U, 18U, 128U,
    227U, 64U, 114U, 54U, 67U, 237U, 27U, 46U, 191U, 45U, 253U, 82U, 245U, 220U, 67U
  };

static uint8_t
vectors_low135[256U] =
  {
    180U, 140U, 19U, 175U, 122U, 155U, 111U, 166U, 56U, 90U, 126U, 229U, 210U, 171U, 151U, 220U,
    235U, 247U, 26U, 113U, 93U, 196U, 101U, 244U, 19U, 203U, 9U, 98U, 41U, 45U, 248U, 76U, 156U,
    131U, 196U, 9U, 51U, 9U, 247U, 73U, 53U, 155U, 10U, 13U, 220U, 193U, 49U, 98U, 203U, 74U, 184U,
    255U, 123U, 58U, 99U, 54U, 53U, 30U, 215U, 158U, 191U, 71U, 115U, 15U, 151U, 172U, 203U, 106U,
    150U, 10U, 156U, 92U, 37U, 224U, 146U, 10U, 6U, 204U, 204U, 59U, 63U, 98U, 182U, 22U, 193U, 92U,
    161U, 141U, 126U, 11U, 92U, 46U, 125U, 138U, 210U, 81U, 141U, 30U, 240U, 190U, 245U, 21U, 175U,
    134U, 104U, 147U, 233U, 55U, 139U, 86U, 222U, 236U, 50U, 130U, 95U, 224U, 162U, 197U, 169U,
    114U, 159U, 101U, 137U, 21U, 185U, 154U, 178U, 42U, 3U, 183U, 24U, 126U, 131U, 210U, 208U, 244U,
    27U, 148U, 103U, 200U, 50U, 111U, 123U, 200U, 113U, 137U, 221U, 138U, 222U, 24U, 179U, 167U,
    237U, 240U, 192U, 234U, 70U, 45U, 194U, 33U, 9U, 236U, 145U, 41U, 76U, 248U, 206U, 105U, 200U,
    205U, 12U, 18U, 155U, 66U, 62U, 218U, 221U, 168U, 251U, 210U, 95U, 73U, 131U, 167U, 13U, 117U,
    0U, 21U, 118U, 162U, 100U, 5U, 24U, 139U, 176U, 40U, 73U, 117U, 32U, 54U, 148U, 195U, 24U, 243U,
    170U, 127U, 228U, 126U, 192U, 65U, 188U, 76U, 17U, 201U, 188U, 235U, 27U, 19U, 31U, 116U, 173U,
    205U, 114U, 252U, 77U, 40U, 19U, 86U, 77U, 230U, 212U, 113U, 16U, 23U, 128U, 3U, 119U, 190U,
    158U, 76U, 87U, 158U, 136U, 70U, 77U, 103U, 234U, 110U, 69U, 122U, 48U, 248U, 246U, 82U, 55U,
    90U
  };

static uint8_t
vectors_low136[32U] =
  {
    70U, 223U, 180U, 232U, 47U, 199U, 132U, 173U, 0U, 148U, 220U, 129U, 19U, 104U, 52U, 229U, 171U,
    199U, 103U, 255U, 242U, 184U, 118U, 160U, 107U, 29U, 189U, 37U, 8U, 219U, 237U, 58U
  };

static uint8_t
vectors_low137[16U] =
  { 100U, 212U, 13U, 56U, 134U, 172U, 21U, 40U, 56U, 246U, 133U, 49U, 33U, 253U, 104U, 183U };

static uint8_t
vectors_low138[32U] =
  {
    50U, 144U, 4U, 184U, 187U, 67U, 147U, 5U, 196U, 178U, 220U, 221U, 84U, 202U, 151U, 164U, 245U,
    76U, 183U, 32U, 168U, 88U, 44U, 220U, 3U, 172U, 38U, 248U, 166U, 3U, 243U, 253U
  };

static uint8_t
vectors_low139[256U] =
  {
    24U, 135U, 235U, 76U, 87U, 182U, 49U, 9U, 247U, 228U, 70U, 191U, 10U, 108U, 89U, 141U, 224U,
    147U, 166U, 1U, 48U, 9U, 80U, 57U, 37U, 214U, 32U, 244U, 12U, 249U, 140U, 135U, 116U, 166U,
    196U, 161U, 175U, 254U, 87U, 248U, 230U, 177U, 144U, 208U, 80U, 79U, 244U, 196U, 235U, 85U,
    186U, 78U, 138U, 38U, 66U, 210U, 48U, 238U, 132U, 94U, 212U, 227U, 29U, 138U, 221U, 219U, 26U,
    33U, 221U, 69U, 52U, 108U, 189U, 169U, 136U, 74U, 50U, 46U, 110U, 143U, 56U, 168U, 46U, 136U,
    143U, 129U, 38U, 74U, 46U, 37U, 78U, 194U, 173U, 90U, 212U, 214U, 10U, 22U, 34U, 135U, 228U,
    139U, 195U, 151U, 118U, 235U, 87U, 220U, 232U, 140U, 254U, 70U, 123U, 4U, 45U, 3U, 125U, 27U,
    6U, 135U, 122U, 204U, 57U, 243U, 27U, 8U, 177U, 170U, 19U, 128U, 95U, 224U, 68U, 10U, 53U, 6U,
    167U, 245U, 157U, 198U, 226U, 55U, 97U, 71U, 172U, 248U, 123U, 120U, 187U, 174U, 244U, 193U,
    91U, 87U, 147U, 53U, 121U, 70U, 136U, 209U, 66U, 238U, 220U, 35U, 24U, 41U, 163U, 74U, 92U,
    105U, 118U, 224U, 200U, 196U, 100U, 158U, 220U, 23U, 140U, 143U, 125U, 143U, 154U, 233U, 47U,
    5U, 227U, 213U, 77U, 246U, 228U, 124U, 249U, 38U, 10U, 90U, 88U, 42U, 125U, 59U, 0U, 48U, 233U,
    165U, 222U, 145U, 45U, 15U, 126U, 77U, 49U, 3U, 35U, 61U, 207U, 168U, 220U, 12U, 174U, 221U,
    241U, 42U, 133U, 2U, 199U, 217U, 65U, 222U, 136U, 54U, 144U, 212U, 123U, 209U, 161U, 182U, 29U,
    114U, 58U, 186U, 240U, 195U, 29U, 103U, 19U, 111U, 180U, 39U, 237U, 202U, 169U, 82U, 106U, 157U,
    201U, 250U
  };

static uint8_t
vectors_low140[32U] =
  {
    18U, 115U, 140U, 13U, 221U, 12U, 156U, 224U, 57U, 61U, 42U, 202U, 189U, 250U, 89U, 34U, 134U,
    7U, 42U, 54U, 46U, 51U, 44U, 163U, 248U, 196U, 1U, 240U, 29U, 97U, 0U, 38U
  };

static uint8_t
vectors_low141[16U] =
  { 185U, 131U, 220U, 253U, 74U, 245U, 228U, 81U, 246U, 239U, 225U, 85U, 252U, 243U, 236U, 20U };

static uint8_t
vectors_low142[32U] =
  {
    7U, 200U, 182U, 152U, 152U, 202U, 236U, 58U, 17U, 4U, 226U, 227U, 11U, 129U, 30U, 160U, 149U,
    56U, 76U, 198U, 54U, 185U, 189U, 36U, 224U, 249U, 131U, 125U, 59U, 142U, 11U, 76U
  };

static uint8_t
vectors_low143[32U] =
  {
    254U, 224U, 104U, 20U, 234U, 182U, 229U, 92U, 183U, 153U, 232U, 21U, 216U, 79U, 7U, 39U, 142U,
    198U, 193U, 45U, 130U, 222U, 161U, 46U, 38U, 28U, 91U, 114U, 208U, 164U, 234U, 165U
  };

static uint8_t
vectors_low144[32U] =
  {
    242U, 146U, 135U, 212U, 109U, 81U, 127U, 9U, 13U, 241U, 26U, 244U, 103U, 3U, 213U, 222U, 119U,
    128U, 40U, 199U, 135U, 163U, 170U, 30U, 89U, 4U, 237U, 115U, 123U, 119U, 105U, 18U
  };

static uint8_t
vectors_low145[32U] =
  {
    12U, 229U, 118U, 202U, 229U, 108U, 70U, 4U, 47U, 242U, 127U, 159U, 17U, 237U, 136U, 241U, 186U,
    83U, 76U, 245U, 242U, 88U, 30U, 90U, 214U, 187U, 105U, 182U, 66U, 137U, 120U, 134U
  };

static uint8_t
vectors_low146[256U] =
  {
    98U, 147U, 16U, 61U, 2U, 133U, 64U, 72U, 76U, 38U, 39U, 112U, 236U, 247U, 196U, 124U, 147U,
    231U, 120U, 218U, 237U, 160U, 165U, 209U, 122U, 131U, 138U, 89U, 51U, 135U, 26U, 240U, 65U,
    172U, 96U, 61U, 129U, 196U, 168U, 215U, 63U, 76U, 172U, 255U, 6U, 206U, 231U, 68U, 36U, 181U,
    126U, 132U, 64U, 232U, 57U, 57U, 80U, 158U, 161U, 134U, 26U, 220U, 170U, 41U, 51U, 43U, 188U,
    224U, 21U, 194U, 180U, 214U, 199U, 65U, 84U, 181U, 42U, 109U, 233U, 180U, 197U, 236U, 158U,
    219U, 79U, 84U, 183U, 190U, 66U, 20U, 43U, 155U, 224U, 123U, 236U, 80U, 82U, 183U, 139U, 188U,
    75U, 183U, 66U, 238U, 137U, 240U, 57U, 144U, 113U, 244U, 154U, 115U, 223U, 135U, 179U, 254U,
    118U, 45U, 22U, 86U, 52U, 108U, 158U, 139U, 248U, 228U, 180U, 184U, 181U, 94U, 78U, 31U, 242U,
    54U, 98U, 182U, 88U, 107U, 240U, 241U, 5U, 233U, 208U, 1U, 241U, 89U, 60U, 23U, 92U, 154U, 35U,
    76U, 187U, 23U, 207U, 218U, 253U, 144U, 186U, 133U, 243U, 71U, 203U, 121U, 176U, 4U, 111U, 181U,
    113U, 91U, 191U, 53U, 240U, 131U, 69U, 200U, 251U, 194U, 110U, 71U, 34U, 66U, 95U, 4U, 186U,
    67U, 28U, 72U, 236U, 255U, 202U, 207U, 21U, 208U, 158U, 165U, 171U, 218U, 146U, 245U, 65U, 228U,
    107U, 182U, 62U, 57U, 51U, 162U, 192U, 83U, 190U, 69U, 101U, 39U, 93U, 52U, 250U, 8U, 91U, 175U,
    85U, 95U, 146U, 244U, 70U, 186U, 94U, 93U, 5U, 250U, 12U, 99U, 197U, 48U, 66U, 9U, 44U, 182U,
    108U, 64U, 109U, 155U, 107U, 54U, 176U, 14U, 118U, 213U, 27U, 73U, 183U, 92U, 54U, 228U, 30U,
    82U
  };

static uint8_t
vectors_low147[32U] =
  {
    106U, 43U, 175U, 144U, 210U, 232U, 184U, 51U, 85U, 160U, 35U, 10U, 143U, 199U, 35U, 124U, 20U,
    15U, 118U, 153U, 244U, 0U, 38U, 226U, 118U, 222U, 174U, 253U, 79U, 170U, 142U, 6U
  };

static uint8_t
vectors_low148[16U] =
  { 178U, 238U, 204U, 230U, 56U, 189U, 159U, 164U, 133U, 233U, 201U, 224U, 217U, 76U, 58U, 120U };

static uint8_t
vectors_low149[32U] =
  {
    169U, 234U, 44U, 75U, 42U, 186U, 31U, 72U, 242U, 199U, 26U, 225U, 167U, 254U, 233U, 14U, 7U,
    57U, 18U, 200U, 51U, 242U, 222U, 156U, 95U, 128U, 42U, 194U, 221U, 197U, 127U, 189U
  };

static uint8_t
vectors_low150[32U] =
  {
    130U, 15U, 201U, 99U, 130U, 113U, 102U, 222U, 113U, 2U, 8U, 167U, 220U, 51U, 147U, 100U, 113U,
    228U, 145U, 252U, 33U, 251U, 1U, 25U, 162U, 82U, 180U, 159U, 239U, 178U, 138U, 1U
  };

static uint8_t
vectors_low151[32U] =
  {
    154U, 70U, 52U, 132U, 209U, 114U, 16U, 136U, 7U, 196U, 60U, 4U, 139U, 209U, 58U, 114U, 209U,
    91U, 71U, 12U, 52U, 67U, 57U, 7U, 116U, 165U, 85U, 114U, 208U, 63U, 71U, 177U
  };

static uint8_t
vectors_low152[32U] =
  {
    217U, 134U, 113U, 151U, 138U, 225U, 75U, 53U, 49U, 57U, 74U, 7U, 133U, 247U, 130U, 66U, 212U,
    179U, 46U, 182U, 28U, 255U, 236U, 96U, 136U, 239U, 184U, 98U, 86U, 147U, 39U, 106U
  };

static uint8_t
vectors_low153[32U] =
  {
    185U, 174U, 243U, 44U, 64U, 183U, 170U, 79U, 215U, 50U, 228U, 67U, 27U, 237U, 206U, 7U, 30U,
    79U, 100U, 64U, 91U, 225U, 200U, 93U, 224U, 60U, 127U, 170U, 10U, 167U, 39U, 15U
  };

static uint8_t
vectors_low154[256U] =
  {
    245U, 87U, 145U, 253U, 201U, 215U, 99U, 195U, 76U, 15U, 196U, 204U, 69U, 122U, 67U, 132U, 150U,
    241U, 143U, 72U, 60U, 198U, 12U, 73U, 63U, 205U, 5U, 73U, 129U, 47U, 173U, 121U, 47U, 146U, 56U,
    21U, 50U, 84U, 138U, 140U, 34U, 87U, 198U, 228U, 36U, 250U, 87U, 10U, 242U, 96U, 189U, 71U,
    222U, 146U, 242U, 72U, 245U, 114U, 145U, 254U, 173U, 58U, 104U, 201U, 75U, 233U, 220U, 18U,
    166U, 86U, 99U, 6U, 34U, 190U, 155U, 96U, 45U, 79U, 197U, 3U, 124U, 41U, 187U, 181U, 250U, 146U,
    254U, 210U, 35U, 81U, 134U, 4U, 143U, 101U, 33U, 49U, 248U, 69U, 240U, 30U, 215U, 24U, 186U,
    240U, 89U, 87U, 232U, 99U, 35U, 158U, 148U, 165U, 97U, 58U, 164U, 125U, 210U, 93U, 91U, 201U,
    241U, 112U, 228U, 4U, 126U, 134U, 239U, 30U, 239U, 166U, 14U, 53U, 159U, 34U, 4U, 163U, 244U,
    83U, 201U, 179U, 125U, 207U, 217U, 65U, 7U, 54U, 238U, 20U, 226U, 150U, 171U, 205U, 193U, 133U,
    243U, 237U, 49U, 216U, 173U, 70U, 26U, 129U, 71U, 159U, 149U, 126U, 105U, 195U, 67U, 52U, 162U,
    78U, 34U, 244U, 166U, 150U, 6U, 219U, 139U, 202U, 108U, 177U, 137U, 231U, 222U, 75U, 131U, 216U,
    161U, 4U, 97U, 251U, 161U, 148U, 44U, 131U, 170U, 46U, 95U, 132U, 220U, 237U, 148U, 64U, 241U,
    10U, 84U, 199U, 65U, 83U, 100U, 50U, 135U, 49U, 58U, 231U, 254U, 27U, 242U, 60U, 106U, 190U,
    204U, 85U, 196U, 163U, 245U, 84U, 4U, 149U, 183U, 210U, 154U, 48U, 45U, 66U, 110U, 226U, 241U,
    61U, 217U, 237U, 122U, 90U, 102U, 24U, 114U, 69U, 68U, 218U, 99U, 82U, 124U, 112U, 46U, 76U
  };

static uint8_t
vectors_low155[32U] =
  {
    71U, 19U, 159U, 84U, 74U, 249U, 246U, 176U, 184U, 2U, 43U, 186U, 229U, 185U, 54U, 163U, 244U,
    191U, 138U, 15U, 28U, 209U, 12U, 140U, 95U, 184U, 187U, 115U, 99U, 223U, 100U, 17U
  };

static uint8_t
vectors_low156[16U] =
  { 185U, 150U, 64U, 247U, 12U, 123U, 85U, 96U, 95U, 123U, 238U, 103U, 83U, 243U, 6U, 117U };

static uint8_t
vectors_low157[32U] =
  {
    15U, 136U, 53U, 117U, 25U, 232U, 242U, 192U, 84U, 149U, 197U, 149U, 5U, 110U, 96U, 35U, 70U,
    11U, 234U, 71U, 231U, 159U, 114U, 177U, 19U, 120U, 78U, 182U, 167U, 127U, 159U, 40U
  };

static uint8_t
vectors_low158[32U] =
  {
    131U, 237U, 127U, 181U, 174U, 133U, 19U, 129U, 97U, 254U, 144U, 177U, 75U, 21U, 41U, 91U, 17U,
    216U, 27U, 14U, 203U, 217U, 241U, 131U, 138U, 40U, 88U, 207U, 158U, 130U, 40U, 134U
  };

static uint8_t
vectors_low159[32U] =
  {
    233U, 115U, 234U, 45U, 57U, 155U, 156U, 74U, 214U, 133U, 65U, 26U, 97U, 155U, 122U, 92U, 230U,
    246U, 86U, 139U, 198U, 110U, 251U, 136U, 85U, 166U, 159U, 37U, 104U, 41U, 166U, 45U
  };

static uint8_t
vectors_low160[32U] =
  {
    27U, 216U, 9U, 1U, 4U, 183U, 136U, 68U, 246U, 214U, 21U, 233U, 59U, 122U, 224U, 201U, 33U, 81U,
    124U, 151U, 115U, 92U, 10U, 170U, 40U, 205U, 238U, 30U, 176U, 161U, 70U, 89U
  };

static uint8_t
vectors_low161[32U] =
  {
    77U, 87U, 208U, 79U, 192U, 162U, 173U, 198U, 235U, 182U, 24U, 241U, 35U, 111U, 238U, 14U, 176U,
    14U, 56U, 255U, 130U, 19U, 127U, 94U, 55U, 91U, 224U, 10U, 209U, 170U, 195U, 94U
  };

static uint8_t
vectors_low162[256U] =
  {
    140U, 76U, 227U, 41U, 42U, 229U, 0U, 85U, 123U, 64U, 228U, 33U, 86U, 101U, 200U, 219U, 92U,
    203U, 161U, 63U, 189U, 45U, 38U, 202U, 141U, 31U, 218U, 217U, 220U, 161U, 88U, 55U, 30U, 192U,
    0U, 60U, 248U, 1U, 253U, 40U, 116U, 26U, 47U, 211U, 29U, 21U, 228U, 192U, 97U, 44U, 104U, 225U,
    159U, 164U, 225U, 156U, 98U, 108U, 228U, 176U, 24U, 67U, 3U, 244U, 84U, 76U, 65U, 74U, 101U,
    65U, 199U, 212U, 172U, 94U, 101U, 85U, 210U, 46U, 33U, 192U, 154U, 9U, 106U, 169U, 236U, 9U,
    201U, 2U, 235U, 103U, 162U, 222U, 158U, 186U, 148U, 183U, 25U, 236U, 27U, 164U, 221U, 93U, 186U,
    254U, 233U, 63U, 205U, 81U, 37U, 34U, 62U, 170U, 224U, 191U, 13U, 142U, 126U, 185U, 46U, 160U,
    97U, 12U, 195U, 43U, 105U, 88U, 76U, 10U, 21U, 101U, 128U, 32U, 40U, 243U, 30U, 105U, 16U, 2U,
    29U, 97U, 142U, 81U, 56U, 19U, 126U, 204U, 171U, 137U, 74U, 83U, 133U, 202U, 69U, 68U, 253U,
    242U, 9U, 25U, 239U, 34U, 22U, 163U, 234U, 244U, 79U, 218U, 204U, 127U, 224U, 92U, 226U, 46U,
    86U, 90U, 90U, 176U, 19U, 205U, 108U, 158U, 10U, 128U, 180U, 48U, 250U, 139U, 114U, 18U, 127U,
    132U, 243U, 167U, 128U, 212U, 238U, 146U, 199U, 41U, 1U, 234U, 252U, 138U, 33U, 197U, 109U,
    204U, 104U, 122U, 196U, 206U, 70U, 76U, 206U, 6U, 136U, 149U, 71U, 27U, 54U, 247U, 181U, 137U,
    135U, 174U, 50U, 114U, 88U, 31U, 0U, 248U, 214U, 103U, 8U, 91U, 222U, 173U, 203U, 6U, 255U,
    239U, 91U, 27U, 50U, 155U, 241U, 219U, 113U, 206U, 16U, 26U, 45U, 105U, 77U, 233U, 227U, 34U
  };

static uint8_t
vectors_low163[32U] =
  {
    40U, 134U, 255U, 78U, 17U, 149U, 12U, 30U, 99U, 147U, 152U, 178U, 199U, 214U, 144U, 141U, 92U,
    46U, 77U, 174U, 183U, 113U, 158U, 109U, 217U, 138U, 57U, 177U, 66U, 142U, 167U, 223U
  };

static uint8_t
vectors_low164[16U] =
  { 140U, 187U, 151U, 245U, 140U, 242U, 67U, 4U, 91U, 218U, 219U, 47U, 155U, 189U, 171U, 16U };

static uint8_t
vectors_low165[32U] =
  {
    244U, 135U, 185U, 75U, 94U, 78U, 218U, 73U, 233U, 51U, 224U, 194U, 104U, 235U, 80U, 66U, 196U,
    34U, 223U, 136U, 6U, 30U, 191U, 253U, 137U, 61U, 57U, 250U, 253U, 88U, 239U, 211U
  };

static uint8_t
vectors_low166[32U] =
  {
    255U, 142U, 118U, 86U, 162U, 27U, 204U, 237U, 8U, 41U, 114U, 113U, 158U, 191U, 135U, 83U, 156U,
    72U, 37U, 203U, 15U, 75U, 234U, 189U, 18U, 161U, 45U, 84U, 77U, 234U, 135U, 175U
  };

static uint8_t
vectors_low167[32U] =
  {
    246U, 77U, 211U, 176U, 239U, 197U, 200U, 193U, 70U, 249U, 185U, 184U, 240U, 236U, 124U, 203U,
    120U, 78U, 135U, 193U, 98U, 104U, 164U, 170U, 179U, 30U, 158U, 221U, 242U, 201U, 184U, 62U
  };

static uint8_t
vectors_low168[32U] =
  {
    157U, 193U, 107U, 149U, 90U, 232U, 5U, 241U, 14U, 187U, 220U, 55U, 148U, 162U, 171U, 230U, 113U,
    163U, 57U, 202U, 20U, 139U, 70U, 239U, 110U, 162U, 8U, 105U, 138U, 84U, 160U, 216U
  };

static uint8_t
vectors_low169[256U] =
  {
    14U, 140U, 156U, 185U, 159U, 236U, 55U, 96U, 43U, 41U, 30U, 80U, 142U, 67U, 194U, 171U, 50U,
    61U, 5U, 118U, 65U, 132U, 55U, 156U, 163U, 162U, 202U, 64U, 128U, 237U, 38U, 194U, 219U, 253U,
    243U, 209U, 145U, 100U, 133U, 199U, 235U, 164U, 144U, 119U, 202U, 136U, 31U, 176U, 61U, 7U,
    249U, 103U, 202U, 217U, 180U, 119U, 149U, 159U, 0U, 122U, 97U, 136U, 21U, 11U, 102U, 48U, 33U,
    138U, 245U, 95U, 221U, 123U, 226U, 235U, 136U, 212U, 139U, 94U, 198U, 182U, 135U, 110U, 194U,
    86U, 101U, 192U, 49U, 6U, 36U, 40U, 61U, 43U, 84U, 96U, 227U, 115U, 111U, 139U, 159U, 11U, 132U,
    9U, 90U, 164U, 117U, 74U, 197U, 144U, 103U, 167U, 204U, 115U, 64U, 44U, 9U, 177U, 118U, 137U,
    114U, 179U, 171U, 212U, 158U, 14U, 35U, 122U, 116U, 22U, 73U, 234U, 120U, 136U, 234U, 74U, 2U,
    76U, 9U, 82U, 185U, 74U, 242U, 124U, 83U, 177U, 58U, 252U, 170U, 79U, 183U, 151U, 111U, 101U,
    68U, 56U, 9U, 209U, 187U, 215U, 228U, 183U, 65U, 188U, 214U, 196U, 163U, 242U, 205U, 248U, 99U,
    231U, 25U, 229U, 213U, 230U, 0U, 67U, 231U, 113U, 206U, 83U, 85U, 222U, 225U, 197U, 41U, 157U,
    223U, 165U, 77U, 119U, 221U, 222U, 41U, 36U, 39U, 28U, 14U, 206U, 30U, 30U, 30U, 138U, 166U,
    33U, 140U, 8U, 174U, 228U, 9U, 147U, 238U, 213U, 137U, 89U, 175U, 67U, 12U, 125U, 83U, 180U,
    23U, 154U, 163U, 85U, 254U, 188U, 196U, 1U, 36U, 203U, 122U, 29U, 41U, 101U, 227U, 104U, 50U,
    229U, 244U, 47U, 154U, 72U, 39U, 88U, 136U, 114U, 92U, 186U, 40U, 215U, 35U, 152U, 251U, 239U,
    172U, 148U
  };

static uint8_t
vectors_low170[32U] =
  {
    40U, 134U, 255U, 78U, 17U, 149U, 12U, 30U, 99U, 147U, 152U, 178U, 199U, 214U, 144U, 141U, 92U,
    46U, 77U, 174U, 183U, 113U, 158U, 109U, 217U, 138U, 57U, 177U, 66U, 142U, 167U, 223U
  };

static uint8_t
vectors_low171[16U] =
  { 140U, 187U, 151U, 245U, 140U, 242U, 67U, 4U, 91U, 218U, 219U, 47U, 155U, 189U, 171U, 16U };

static uint8_t
vectors_low172[32U] =
  {
    244U, 135U, 185U, 75U, 94U, 78U, 218U, 73U, 233U, 51U, 224U, 194U, 104U, 235U, 80U, 66U, 196U,
    34U, 223U, 136U, 6U, 30U, 191U, 253U, 137U, 61U, 57U, 250U, 253U, 88U, 239U, 211U
  };

static uint8_t
vectors_low173[32U] =
  {
    255U, 142U, 118U, 86U, 162U, 27U, 204U, 237U, 8U, 41U, 114U, 113U, 158U, 191U, 135U, 83U, 156U,
    72U, 37U, 203U, 15U, 75U, 234U, 189U, 18U, 161U, 45U, 84U, 77U, 234U, 135U, 175U
  };

static uint8_t
vectors_low174[32U] =
  {
    246U, 77U, 211U, 176U, 239U, 197U, 200U, 193U, 70U, 249U, 185U, 184U, 240U, 236U, 124U, 203U,
    120U, 78U, 135U, 193U, 98U, 104U, 164U, 170U, 179U, 30U, 158U, 221U, 242U, 201U, 184U, 62U
  };

static uint8_t
vectors_low175[32U] =
  {
    157U, 193U, 107U, 149U, 90U, 232U, 5U, 241U, 14U, 187U, 220U, 55U, 148U, 162U, 171U, 230U, 113U,
    163U, 57U, 202U, 20U, 139U, 70U, 239U, 110U, 162U, 8U, 105U, 138U, 84U, 160U, 216U
  };

static uint8_t
vectors_low176[255U] =
  {
    14U, 140U, 156U, 185U, 159U, 236U, 55U, 96U, 43U, 41U, 30U, 80U, 142U, 67U, 194U, 171U, 50U,
    61U, 5U, 118U, 65U, 132U, 55U, 156U, 163U, 162U, 202U, 64U, 128U, 237U, 38U, 194U, 219U, 253U,
    243U, 209U, 145U, 100U, 133U, 199U, 235U, 164U, 144U, 119U, 202U, 136U, 31U, 176U, 61U, 7U,
    249U, 103U, 202U, 217U, 180U, 119U, 149U, 159U, 0U, 122U, 97U, 136U, 21U, 11U, 102U, 48U, 33U,
    138U, 245U, 95U, 221U, 123U, 226U, 235U, 136U, 212U, 139U, 94U, 198U, 182U, 135U, 110U, 194U,
    86U, 101U, 192U, 49U, 6U, 36U, 40U, 61U, 43U, 84U, 96U, 227U, 115U, 111U, 139U, 159U, 11U, 132U,
    9U, 90U, 164U, 117U, 74U, 197U, 144U, 103U, 167U, 204U, 115U, 64U, 44U, 9U, 177U, 118U, 137U,
    114U, 179U, 171U, 212U, 158U, 14U, 35U, 122U, 116U, 22U, 73U, 234U, 120U, 136U, 234U, 74U, 2U,
    76U, 9U, 82U, 185U, 74U, 242U, 124U, 83U, 177U, 58U, 252U, 170U, 79U, 183U, 151U, 111U, 101U,
    68U, 56U, 9U, 209U, 187U, 215U, 228U, 183U, 65U, 188U, 214U, 196U, 163U, 242U, 205U, 248U, 99U,
    231U, 25U, 229U, 213U, 230U, 0U, 67U, 231U, 113U, 206U, 83U, 85U, 222U, 225U, 197U, 41U, 157U,
    223U, 165U, 77U, 119U, 221U, 222U, 41U, 36U, 39U, 28U, 14U, 206U, 30U, 30U, 30U, 138U, 166U,
    33U, 140U, 8U, 174U, 228U, 9U, 147U, 238U, 213U, 137U, 89U, 175U, 67U, 12U, 125U, 83U, 180U,
    23U, 154U, 163U, 85U, 254U, 188U, 196U, 1U, 36U, 203U, 122U, 29U, 41U, 101U, 227U, 104U, 50U,
    229U, 244U, 47U, 154U, 72U, 39U, 88U, 136U, 114U, 92U, 186U, 40U, 215U, 35U, 152U, 251U, 239U,
    172U
  };

typedef struct lbuffer__uint8_t_s
{
  uint32_t len;
  uint8_t *b;
}
lbuffer__uint8_t;

typedef struct __Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_s
{
  lbuffer__uint8_t fst;
  lbuffer__uint8_t snd;
}
__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t;

typedef struct
__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t_s
{
  hash_alg fst;
  lbuffer__uint8_t snd;
  lbuffer__uint8_t thd;
  lbuffer__uint8_t f3;
  lbuffer__uint8_t f4;
  lbuffer__uint8_t f5;
  __Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t f6;
  lbuffer__uint8_t f7;
}
__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t;

static __Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t
vectors_low177[28U] =
  {
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA1,
        .snd = { .len = 16U, .b = vectors_low0 },
        .thd = { .len = 8U, .b = vectors_low1 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 16U, .b = vectors_low2 },
        .f5 = { .len = 16U, .b = vectors_low3 },
        .f6 = { .fst = { .len = 16U, .b = vectors_low4 }, .snd = { .len = 16U, .b = vectors_low5 } },
        .f7 = { .len = 80U, .b = vectors_low6 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA1,
        .snd = { .len = 16U, .b = vectors_low7 },
        .thd = { .len = 8U, .b = vectors_low8 },
        .f3 = { .len = 16U, .b = vectors_low9 },
        .f4 = { .len = 16U, .b = vectors_low10 },
        .f5 = { .len = 16U, .b = vectors_low11 },
        .f6 = {
          .fst = { .len = 16U, .b = vectors_low12 },
          .snd = { .len = 16U, .b = vectors_low13 }
        },
        .f7 = { .len = 80U, .b = vectors_low14 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA1,
        .snd = { .len = 16U, .b = vectors_low15 },
        .thd = { .len = 8U, .b = vectors_low16 },
        .f3 = { .len = 16U, .b = vectors_low17 },
        .f4 = { .len = 16U, .b = vectors_low18 },
        .f5 = { .len = 0U, .b = NULL },
        .f6 = { .fst = { .len = 0U, .b = NULL }, .snd = { .len = 0U, .b = NULL } },
        .f7 = { .len = 80U, .b = vectors_low19 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA1,
        .snd = { .len = 16U, .b = vectors_low20 },
        .thd = { .len = 8U, .b = vectors_low21 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 16U, .b = vectors_low22 },
        .f5 = { .len = 0U, .b = NULL },
        .f6 = { .fst = { .len = 0U, .b = NULL }, .snd = { .len = 0U, .b = NULL } },
        .f7 = { .len = 80U, .b = vectors_low23 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA1,
        .snd = { .len = 16U, .b = vectors_low24 },
        .thd = { .len = 8U, .b = vectors_low25 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 16U, .b = vectors_low26 },
        .f5 = { .len = 16U, .b = vectors_low27 },
        .f6 = {
          .fst = { .len = 16U, .b = vectors_low28 },
          .snd = { .len = 16U, .b = vectors_low29 }
        },
        .f7 = { .len = 80U, .b = vectors_low30 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA1,
        .snd = { .len = 16U, .b = vectors_low31 },
        .thd = { .len = 8U, .b = vectors_low32 },
        .f3 = { .len = 16U, .b = vectors_low33 },
        .f4 = { .len = 16U, .b = vectors_low34 },
        .f5 = { .len = 16U, .b = vectors_low35 },
        .f6 = {
          .fst = { .len = 16U, .b = vectors_low36 },
          .snd = { .len = 16U, .b = vectors_low37 }
        },
        .f7 = { .len = 80U, .b = vectors_low38 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_256,
        .snd = { .len = 32U, .b = vectors_low39 },
        .thd = { .len = 16U, .b = vectors_low40 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 32U, .b = vectors_low41 },
        .f5 = { .len = 32U, .b = vectors_low42 },
        .f6 = {
          .fst = { .len = 32U, .b = vectors_low43 },
          .snd = { .len = 32U, .b = vectors_low44 }
        },
        .f7 = { .len = 128U, .b = vectors_low45 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_256,
        .snd = { .len = 32U, .b = vectors_low46 },
        .thd = { .len = 16U, .b = vectors_low47 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 32U, .b = vectors_low48 },
        .f5 = { .len = 32U, .b = vectors_low49 },
        .f6 = {
          .fst = { .len = 32U, .b = vectors_low50 },
          .snd = { .len = 32U, .b = vectors_low51 }
        },
        .f7 = { .len = 128U, .b = vectors_low52 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_256,
        .snd = { .len = 32U, .b = vectors_low53 },
        .thd = { .len = 16U, .b = vectors_low54 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 32U, .b = vectors_low55 },
        .f5 = { .len = 32U, .b = vectors_low56 },
        .f6 = {
          .fst = { .len = 32U, .b = vectors_low57 },
          .snd = { .len = 32U, .b = vectors_low58 }
        },
        .f7 = { .len = 128U, .b = vectors_low59 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_256,
        .snd = { .len = 32U, .b = vectors_low60 },
        .thd = { .len = 16U, .b = vectors_low61 },
        .f3 = { .len = 32U, .b = vectors_low62 },
        .f4 = { .len = 32U, .b = vectors_low63 },
        .f5 = { .len = 32U, .b = vectors_low64 },
        .f6 = {
          .fst = { .len = 32U, .b = vectors_low65 },
          .snd = { .len = 32U, .b = vectors_low66 }
        },
        .f7 = { .len = 128U, .b = vectors_low67 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_256,
        .snd = { .len = 32U, .b = vectors_low68 },
        .thd = { .len = 16U, .b = vectors_low69 },
        .f3 = { .len = 32U, .b = vectors_low70 },
        .f4 = { .len = 32U, .b = vectors_low71 },
        .f5 = { .len = 0U, .b = NULL },
        .f6 = { .fst = { .len = 0U, .b = NULL }, .snd = { .len = 0U, .b = NULL } },
        .f7 = { .len = 128U, .b = vectors_low72 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_256,
        .snd = { .len = 32U, .b = vectors_low73 },
        .thd = { .len = 16U, .b = vectors_low74 },
        .f3 = { .len = 32U, .b = vectors_low75 },
        .f4 = { .len = 32U, .b = vectors_low76 },
        .f5 = { .len = 32U, .b = vectors_low77 },
        .f6 = {
          .fst = { .len = 32U, .b = vectors_low78 },
          .snd = { .len = 32U, .b = vectors_low79 }
        },
        .f7 = { .len = 128U, .b = vectors_low80 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_256,
        .snd = { .len = 32U, .b = vectors_low81 },
        .thd = { .len = 16U, .b = vectors_low82 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 32U, .b = vectors_low83 },
        .f5 = { .len = 32U, .b = vectors_low84 },
        .f6 = {
          .fst = { .len = 32U, .b = vectors_low85 },
          .snd = { .len = 32U, .b = vectors_low86 }
        },
        .f7 = { .len = 128U, .b = vectors_low87 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_256,
        .snd = { .len = 32U, .b = vectors_low88 },
        .thd = { .len = 16U, .b = vectors_low89 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 32U, .b = vectors_low90 },
        .f5 = { .len = 0U, .b = NULL },
        .f6 = { .fst = { .len = 0U, .b = NULL }, .snd = { .len = 0U, .b = NULL } },
        .f7 = { .len = 128U, .b = vectors_low91 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_256,
        .snd = { .len = 32U, .b = vectors_low92 },
        .thd = { .len = 16U, .b = vectors_low93 },
        .f3 = { .len = 32U, .b = vectors_low94 },
        .f4 = { .len = 32U, .b = vectors_low95 },
        .f5 = { .len = 0U, .b = NULL },
        .f6 = { .fst = { .len = 0U, .b = NULL }, .snd = { .len = 0U, .b = NULL } },
        .f7 = { .len = 128U, .b = vectors_low96 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_384,
        .snd = { .len = 32U, .b = vectors_low97 },
        .thd = { .len = 16U, .b = vectors_low98 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 32U, .b = vectors_low99 },
        .f5 = { .len = 32U, .b = vectors_low100 },
        .f6 = {
          .fst = { .len = 32U, .b = vectors_low101 },
          .snd = { .len = 32U, .b = vectors_low102 }
        },
        .f7 = { .len = 192U, .b = vectors_low103 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_384,
        .snd = { .len = 32U, .b = vectors_low104 },
        .thd = { .len = 16U, .b = vectors_low105 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 32U, .b = vectors_low106 },
        .f5 = { .len = 0U, .b = NULL },
        .f6 = { .fst = { .len = 0U, .b = NULL }, .snd = { .len = 0U, .b = NULL } },
        .f7 = { .len = 192U, .b = vectors_low107 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_384,
        .snd = { .len = 32U, .b = vectors_low108 },
        .thd = { .len = 16U, .b = vectors_low109 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 32U, .b = vectors_low110 },
        .f5 = { .len = 32U, .b = vectors_low111 },
        .f6 = {
          .fst = { .len = 32U, .b = vectors_low112 },
          .snd = { .len = 32U, .b = vectors_low113 }
        },
        .f7 = { .len = 192U, .b = vectors_low114 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_512,
        .snd = { .len = 32U, .b = vectors_low115 },
        .thd = { .len = 16U, .b = vectors_low116 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 32U, .b = vectors_low117 },
        .f5 = { .len = 0U, .b = NULL },
        .f6 = { .fst = { .len = 0U, .b = NULL }, .snd = { .len = 0U, .b = NULL } },
        .f7 = { .len = 256U, .b = vectors_low118 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_512,
        .snd = { .len = 32U, .b = vectors_low119 },
        .thd = { .len = 16U, .b = vectors_low120 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 32U, .b = vectors_low121 },
        .f5 = { .len = 0U, .b = NULL },
        .f6 = { .fst = { .len = 0U, .b = NULL }, .snd = { .len = 0U, .b = NULL } },
        .f7 = { .len = 256U, .b = vectors_low122 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_512,
        .snd = { .len = 32U, .b = vectors_low123 },
        .thd = { .len = 16U, .b = vectors_low124 },
        .f3 = { .len = 32U, .b = vectors_low125 },
        .f4 = { .len = 32U, .b = vectors_low126 },
        .f5 = { .len = 0U, .b = NULL },
        .f6 = { .fst = { .len = 0U, .b = NULL }, .snd = { .len = 0U, .b = NULL } },
        .f7 = { .len = 256U, .b = vectors_low127 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_512,
        .snd = { .len = 32U, .b = vectors_low128 },
        .thd = { .len = 16U, .b = vectors_low129 },
        .f3 = { .len = 32U, .b = vectors_low130 },
        .f4 = { .len = 32U, .b = vectors_low131 },
        .f5 = { .len = 32U, .b = vectors_low132 },
        .f6 = {
          .fst = { .len = 32U, .b = vectors_low133 },
          .snd = { .len = 32U, .b = vectors_low134 }
        },
        .f7 = { .len = 256U, .b = vectors_low135 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_512,
        .snd = { .len = 32U, .b = vectors_low136 },
        .thd = { .len = 16U, .b = vectors_low137 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 32U, .b = vectors_low138 },
        .f5 = { .len = 0U, .b = NULL },
        .f6 = { .fst = { .len = 0U, .b = NULL }, .snd = { .len = 0U, .b = NULL } },
        .f7 = { .len = 256U, .b = vectors_low139 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_512,
        .snd = { .len = 32U, .b = vectors_low140 },
        .thd = { .len = 16U, .b = vectors_low141 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 32U, .b = vectors_low142 },
        .f5 = { .len = 32U, .b = vectors_low143 },
        .f6 = {
          .fst = { .len = 32U, .b = vectors_low144 },
          .snd = { .len = 32U, .b = vectors_low145 }
        },
        .f7 = { .len = 256U, .b = vectors_low146 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_512,
        .snd = { .len = 32U, .b = vectors_low147 },
        .thd = { .len = 16U, .b = vectors_low148 },
        .f3 = { .len = 32U, .b = vectors_low149 },
        .f4 = { .len = 32U, .b = vectors_low150 },
        .f5 = { .len = 32U, .b = vectors_low151 },
        .f6 = {
          .fst = { .len = 32U, .b = vectors_low152 },
          .snd = { .len = 32U, .b = vectors_low153 }
        },
        .f7 = { .len = 256U, .b = vectors_low154 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_512,
        .snd = { .len = 32U, .b = vectors_low155 },
        .thd = { .len = 16U, .b = vectors_low156 },
        .f3 = { .len = 32U, .b = vectors_low157 },
        .f4 = { .len = 32U, .b = vectors_low158 },
        .f5 = { .len = 32U, .b = vectors_low159 },
        .f6 = {
          .fst = { .len = 32U, .b = vectors_low160 },
          .snd = { .len = 32U, .b = vectors_low161 }
        },
        .f7 = { .len = 256U, .b = vectors_low162 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_512,
        .snd = { .len = 32U, .b = vectors_low163 },
        .thd = { .len = 16U, .b = vectors_low164 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 32U, .b = vectors_low165 },
        .f5 = { .len = 32U, .b = vectors_low166 },
        .f6 = {
          .fst = { .len = 32U, .b = vectors_low167 },
          .snd = { .len = 32U, .b = vectors_low168 }
        },
        .f7 = { .len = 256U, .b = vectors_low169 }
      }
    ),
    (
      (__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t){
        .fst = SHA2_512,
        .snd = { .len = 32U, .b = vectors_low170 },
        .thd = { .len = 16U, .b = vectors_low171 },
        .f3 = { .len = 0U, .b = NULL },
        .f4 = { .len = 32U, .b = vectors_low172 },
        .f5 = { .len = 32U, .b = vectors_low173 },
        .f6 = {
          .fst = { .len = 32U, .b = vectors_low174 },
          .snd = { .len = 32U, .b = vectors_low175 }
        },
        .f7 = { .len = 255U, .b = vectors_low176 }
      }
    )
  };

typedef struct
lbuffer__K___Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t_s
{
  uint32_t len;
  __Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t
  *b;
}
lbuffer__K___Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t;

static lbuffer__K___Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t
vectors_low = { .len = 28U, .b = vectors_low177 };

static bool compare_and_print(uint8_t *b1, uint8_t *b2, uint32_t len)
{
  LowStar_Printf_print_string("Expected: ");
  LowStar_Printf_print_lmbuffer_u8(len, (uint8_t *)b1);
  LowStar_Printf_print_string("\n");
  LowStar_Printf_print_string("Computed: ");
  LowStar_Printf_print_lmbuffer_u8(len, (uint8_t *)b2);
  LowStar_Printf_print_string("\n");
  uint8_t res = 255U;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(b1[i], b2[i]);
    res = (uint32_t)uu____0 & (uint32_t)res;
  }
  uint8_t z = res;
  bool b = z == 255U;
  if (b)
  {
    LowStar_Printf_print_string("PASS\n");
  }
  else
  {
    LowStar_Printf_print_string("FAIL\n");
  }
  return b;
}

static void
test_one(
  __Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t
  vec
)
{
  uint8_t *returned_bits = vec.f7.b;
  uint32_t returned_bits_len = vec.f7.len;
  uint8_t *additional_input_2 = vec.f6.snd.b;
  uint32_t additional_input_2_len = vec.f6.snd.len;
  uint8_t *additional_input_1 = vec.f6.fst.b;
  uint32_t additional_input_1_len = vec.f6.fst.len;
  uint8_t *additional_input_reseed = vec.f5.b;
  uint32_t additional_input_reseed_len = vec.f5.len;
  uint8_t *entropy_input_reseed = vec.f4.b;
  uint32_t entropy_input_reseed_len = vec.f4.len;
  uint8_t *personalization_string = vec.f3.b;
  uint32_t personalization_string_len = vec.f3.len;
  uint8_t *nonce = vec.thd.b;
  uint32_t nonce_len = vec.thd.len;
  uint8_t *entropy_input = vec.snd.b;
  uint32_t entropy_input_len = vec.snd.len;
  hash_alg a = vec.fst;
  if
  (
    !(is_supported_alg(a)
    && min_length(a) <= entropy_input_len
    && entropy_input_len <= max_length
    && min_length(a) / 2U <= nonce_len
    && nonce_len <= max_length
    && personalization_string_len <= max_personalization_string_length
    && min_length(a) <= entropy_input_reseed_len
    && entropy_input_reseed_len <= max_length
    && additional_input_reseed_len <= max_additional_input_length
    && additional_input_1_len <= max_additional_input_length
    && additional_input_2_len <= max_additional_input_length
    && 0U < returned_bits_len
    && returned_bits_len <= max_output_length)
  )
  {
    exit((int32_t)-1);
  }
  else
  {
    KRML_CHECK_SIZE(sizeof (uint8_t), returned_bits_len);
    uint8_t output[returned_bits_len];
    memset(output, 0U, returned_bits_len * sizeof (uint8_t));
    uint8_t *k;
    uint8_t buf0[20U] = { 0U };
    uint8_t buf1[32U] = { 0U };
    uint8_t buf2[48U] = { 0U };
    uint8_t buf3[64U] = { 0U };
    switch (a)
    {
      case SHA1:
        {
          k = buf0;
          break;
        }
      case SHA2_256:
        {
          k = buf1;
          break;
        }
      case SHA2_384:
        {
          k = buf2;
          break;
        }
      case SHA2_512:
        {
          k = buf3;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    uint8_t *v;
    uint8_t buf4[20U] = { 0U };
    uint8_t buf5[32U] = { 0U };
    uint8_t buf6[48U] = { 0U };
    uint8_t buf[64U] = { 0U };
    switch (a)
    {
      case SHA1:
        {
          v = buf4;
          break;
        }
      case SHA2_256:
        {
          v = buf5;
          break;
        }
      case SHA2_384:
        {
          v = buf6;
          break;
        }
      case SHA2_512:
        {
          v = buf;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    uint32_t ctr = 1U;
    state st = { .k = k, .v = v, .reseed_counter = &ctr };
    instantiate(a,
      st,
      entropy_input_len,
      entropy_input,
      nonce_len,
      nonce,
      personalization_string_len,
      personalization_string);
    reseed(a,
      st,
      entropy_input_reseed_len,
      entropy_input_reseed,
      additional_input_reseed_len,
      additional_input_reseed);
    bool
    ok = generate(a, output, st, returned_bits_len, additional_input_1_len, additional_input_1);
    if (ok)
    {
      bool
      ok1 = generate(a, output, st, returned_bits_len, additional_input_2_len, additional_input_2);
      if (ok1)
      {
        bool ok2 = compare_and_print(returned_bits, output, returned_bits_len);
        if (!ok2)
        {
          exit((int32_t)1);
        }
      }
      else
      {
        exit((int32_t)1);
      }
    }
    else
    {
      exit((int32_t)1);
    }
  }
}

exit_code main(void)
{
  C_String_print("[HMAC_DRBG]");
  C_String_print("\n");
  uint32_t len = vectors_low.len;
  __Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t__Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t__Test_Lowstarize_lbuffer__uint8_t
  *vs = vectors_low.b;
  for (uint32_t i = 0U; i < len; i++)
  {
    LowStar_Printf_print_string("HMAC-DRBG Test ");
    LowStar_Printf_print_u32(i + 1U);
    LowStar_Printf_print_string("/");
    LowStar_Printf_print_u32(len);
    LowStar_Printf_print_string("\n");
    test_one(vs[i]);
  }
  return EXIT_SUCCESS;
}

