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


#include "Hacl_Test_SHA2.h"

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

static inline void sha224_init(uint32_t *hash)
{
  for (uint32_t i = 0U; i < 8U; i++)
  {
    uint32_t *os = hash;
    uint32_t x = Hacl_Impl_SHA2_Generic_h224[i];
    os[i] = x;
  }
}

static inline void sha224_update_nblocks(uint32_t len, uint8_t *b, uint32_t *st)
{
  sha256_update_nblocks(len, b, st);
}

static void sha224_update_last(uint64_t totlen, uint32_t len, uint8_t *b, uint32_t *st)
{
  sha256_update_last(totlen, len, b, st);
}

static inline void sha224_finish(uint32_t *st, uint8_t *h)
{
  uint8_t hbuf[32U] = { 0U };
  for (uint32_t i = 0U; i < 8U; i++)
  {
    store32_be(hbuf + i * 4U, st[i]);
  }
  memcpy(h, hbuf, 28U * sizeof (uint8_t));
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
Hash `input`, of len `input_len`, into `output`, an array of 28 bytes.
*/
static void hash_224(uint8_t *output, uint8_t *input, uint32_t input_len)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint32_t st[8U] = { 0U };
  sha224_init(st);
  uint32_t rem = input_len % 64U;
  uint64_t len_ = (uint64_t)input_len;
  sha224_update_nblocks(input_len, ib, st);
  uint32_t rem1 = input_len % 64U;
  uint8_t *b0 = ib;
  uint8_t *lb = b0 + input_len - rem1;
  sha224_update_last(len_, rem, lb, st);
  sha224_finish(st, rb);
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

extern bool
Lib_PrintBuffer_result_compare_display(uint32_t len, const uint8_t *buf0, const uint8_t *buf1);

static void
test_sha2(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *expected224,
  uint8_t *expected256,
  uint8_t *expected384,
  uint8_t *expected512
)
{
  uint8_t test224[28U] = { 0U };
  uint8_t test256[32U] = { 0U };
  uint8_t test384[48U] = { 0U };
  uint8_t test512[64U] = { 0U };
  hash_224(test224, msg, msg_len);
  hash_256(test256, msg, msg_len);
  hash_384(test384, msg, msg_len);
  hash_512(test512, msg, msg_len);
  if (!Lib_PrintBuffer_result_compare_display(28U, test224, expected224))
  {
    exit((int32_t)255);
  }
  if (!Lib_PrintBuffer_result_compare_display(32U, test256, expected256))
  {
    exit((int32_t)255);
  }
  if (!Lib_PrintBuffer_result_compare_display(48U, test384, expected384))
  {
    exit((int32_t)255);
  }
  if (!Lib_PrintBuffer_result_compare_display(64U, test512, expected512))
  {
    exit((int32_t)255);
  }
}

static uint8_t test1_plaintext[3U] = { 0x61U, 0x62U, 0x63U };

static uint8_t
test1_expected_sha2_224[28U] =
  {
    0x23U, 0x09U, 0x7dU, 0x22U, 0x34U, 0x05U, 0xd8U, 0x22U, 0x86U, 0x42U, 0xa4U, 0x77U, 0xbdU,
    0xa2U, 0x55U, 0xb3U, 0x2aU, 0xadU, 0xbcU, 0xe4U, 0xbdU, 0xa0U, 0xb3U, 0xf7U, 0xe3U, 0x6cU,
    0x9dU, 0xa7U
  };

static uint8_t
test1_expected_sha2_256[32U] =
  {
    0xbaU, 0x78U, 0x16U, 0xbfU, 0x8fU, 0x01U, 0xcfU, 0xeaU, 0x41U, 0x41U, 0x40U, 0xdeU, 0x5dU,
    0xaeU, 0x22U, 0x23U, 0xb0U, 0x03U, 0x61U, 0xa3U, 0x96U, 0x17U, 0x7aU, 0x9cU, 0xb4U, 0x10U,
    0xffU, 0x61U, 0xf2U, 0x00U, 0x15U, 0xadU
  };

static uint8_t
test1_expected_sha2_384[48U] =
  {
    0xcbU, 0x00U, 0x75U, 0x3fU, 0x45U, 0xa3U, 0x5eU, 0x8bU, 0xb5U, 0xa0U, 0x3dU, 0x69U, 0x9aU,
    0xc6U, 0x50U, 0x07U, 0x27U, 0x2cU, 0x32U, 0xabU, 0x0eU, 0xdeU, 0xd1U, 0x63U, 0x1aU, 0x8bU,
    0x60U, 0x5aU, 0x43U, 0xffU, 0x5bU, 0xedU, 0x80U, 0x86U, 0x07U, 0x2bU, 0xa1U, 0xe7U, 0xccU,
    0x23U, 0x58U, 0xbaU, 0xecU, 0xa1U, 0x34U, 0xc8U, 0x25U, 0xa7U
  };

static uint8_t
test1_expected_sha2_512[64U] =
  {
    0xddU, 0xafU, 0x35U, 0xa1U, 0x93U, 0x61U, 0x7aU, 0xbaU, 0xccU, 0x41U, 0x73U, 0x49U, 0xaeU,
    0x20U, 0x41U, 0x31U, 0x12U, 0xe6U, 0xfaU, 0x4eU, 0x89U, 0xa9U, 0x7eU, 0xa2U, 0x0aU, 0x9eU,
    0xeeU, 0xe6U, 0x4bU, 0x55U, 0xd3U, 0x9aU, 0x21U, 0x92U, 0x99U, 0x2aU, 0x27U, 0x4fU, 0xc1U,
    0xa8U, 0x36U, 0xbaU, 0x3cU, 0x23U, 0xa3U, 0xfeU, 0xebU, 0xbdU, 0x45U, 0x4dU, 0x44U, 0x23U,
    0x64U, 0x3cU, 0xe8U, 0x0eU, 0x2aU, 0x9aU, 0xc9U, 0x4fU, 0xa5U, 0x4cU, 0xa4U, 0x9fU
  };

static uint8_t test2_plaintext[0U] = {  };

static uint8_t
test2_expected_sha2_224[28U] =
  {
    0xd1U, 0x4aU, 0x02U, 0x8cU, 0x2aU, 0x3aU, 0x2bU, 0xc9U, 0x47U, 0x61U, 0x02U, 0xbbU, 0x28U,
    0x82U, 0x34U, 0xc4U, 0x15U, 0xa2U, 0xb0U, 0x1fU, 0x82U, 0x8eU, 0xa6U, 0x2aU, 0xc5U, 0xb3U,
    0xe4U, 0x2fU
  };

static uint8_t
test2_expected_sha2_256[32U] =
  {
    0xe3U, 0xb0U, 0xc4U, 0x42U, 0x98U, 0xfcU, 0x1cU, 0x14U, 0x9aU, 0xfbU, 0xf4U, 0xc8U, 0x99U,
    0x6fU, 0xb9U, 0x24U, 0x27U, 0xaeU, 0x41U, 0xe4U, 0x64U, 0x9bU, 0x93U, 0x4cU, 0xa4U, 0x95U,
    0x99U, 0x1bU, 0x78U, 0x52U, 0xb8U, 0x55U
  };

static uint8_t
test2_expected_sha2_384[48U] =
  {
    0x38U, 0xb0U, 0x60U, 0xa7U, 0x51U, 0xacU, 0x96U, 0x38U, 0x4cU, 0xd9U, 0x32U, 0x7eU, 0xb1U,
    0xb1U, 0xe3U, 0x6aU, 0x21U, 0xfdU, 0xb7U, 0x11U, 0x14U, 0xbeU, 0x07U, 0x43U, 0x4cU, 0x0cU,
    0xc7U, 0xbfU, 0x63U, 0xf6U, 0xe1U, 0xdaU, 0x27U, 0x4eU, 0xdeU, 0xbfU, 0xe7U, 0x6fU, 0x65U,
    0xfbU, 0xd5U, 0x1aU, 0xd2U, 0xf1U, 0x48U, 0x98U, 0xb9U, 0x5bU
  };

static uint8_t
test2_expected_sha2_512[64U] =
  {
    0xcfU, 0x83U, 0xe1U, 0x35U, 0x7eU, 0xefU, 0xb8U, 0xbdU, 0xf1U, 0x54U, 0x28U, 0x50U, 0xd6U,
    0x6dU, 0x80U, 0x07U, 0xd6U, 0x20U, 0xe4U, 0x05U, 0x0bU, 0x57U, 0x15U, 0xdcU, 0x83U, 0xf4U,
    0xa9U, 0x21U, 0xd3U, 0x6cU, 0xe9U, 0xceU, 0x47U, 0xd0U, 0xd1U, 0x3cU, 0x5dU, 0x85U, 0xf2U,
    0xb0U, 0xffU, 0x83U, 0x18U, 0xd2U, 0x87U, 0x7eU, 0xecU, 0x2fU, 0x63U, 0xb9U, 0x31U, 0xbdU,
    0x47U, 0x41U, 0x7aU, 0x81U, 0xa5U, 0x38U, 0x32U, 0x7aU, 0xf9U, 0x27U, 0xdaU, 0x3eU
  };

static uint8_t
test3_plaintext[56U] =
  {
    0x61U, 0x62U, 0x63U, 0x64U, 0x62U, 0x63U, 0x64U, 0x65U, 0x63U, 0x64U, 0x65U, 0x66U, 0x64U,
    0x65U, 0x66U, 0x67U, 0x65U, 0x66U, 0x67U, 0x68U, 0x66U, 0x67U, 0x68U, 0x69U, 0x67U, 0x68U,
    0x69U, 0x6aU, 0x68U, 0x69U, 0x6aU, 0x6bU, 0x69U, 0x6aU, 0x6bU, 0x6cU, 0x6aU, 0x6bU, 0x6cU,
    0x6dU, 0x6bU, 0x6cU, 0x6dU, 0x6eU, 0x6cU, 0x6dU, 0x6eU, 0x6fU, 0x6dU, 0x6eU, 0x6fU, 0x70U,
    0x6eU, 0x6fU, 0x70U, 0x71U
  };

static uint8_t
test3_expected_sha2_224[28U] =
  {
    0x75U, 0x38U, 0x8bU, 0x16U, 0x51U, 0x27U, 0x76U, 0xccU, 0x5dU, 0xbaU, 0x5dU, 0xa1U, 0xfdU,
    0x89U, 0x01U, 0x50U, 0xb0U, 0xc6U, 0x45U, 0x5cU, 0xb4U, 0xf5U, 0x8bU, 0x19U, 0x52U, 0x52U,
    0x25U, 0x25U
  };

static uint8_t
test3_expected_sha2_256[32U] =
  {
    0x24U, 0x8dU, 0x6aU, 0x61U, 0xd2U, 0x06U, 0x38U, 0xb8U, 0xe5U, 0xc0U, 0x26U, 0x93U, 0x0cU,
    0x3eU, 0x60U, 0x39U, 0xa3U, 0x3cU, 0xe4U, 0x59U, 0x64U, 0xffU, 0x21U, 0x67U, 0xf6U, 0xecU,
    0xedU, 0xd4U, 0x19U, 0xdbU, 0x06U, 0xc1U
  };

static uint8_t
test3_expected_sha2_384[48U] =
  {
    0x33U, 0x91U, 0xfdU, 0xddU, 0xfcU, 0x8dU, 0xc7U, 0x39U, 0x37U, 0x07U, 0xa6U, 0x5bU, 0x1bU,
    0x47U, 0x09U, 0x39U, 0x7cU, 0xf8U, 0xb1U, 0xd1U, 0x62U, 0xafU, 0x05U, 0xabU, 0xfeU, 0x8fU,
    0x45U, 0x0dU, 0xe5U, 0xf3U, 0x6bU, 0xc6U, 0xb0U, 0x45U, 0x5aU, 0x85U, 0x20U, 0xbcU, 0x4eU,
    0x6fU, 0x5fU, 0xe9U, 0x5bU, 0x1fU, 0xe3U, 0xc8U, 0x45U, 0x2bU
  };

static uint8_t
test3_expected_sha2_512[64U] =
  {
    0x20U, 0x4aU, 0x8fU, 0xc6U, 0xddU, 0xa8U, 0x2fU, 0x0aU, 0x0cU, 0xedU, 0x7bU, 0xebU, 0x8eU,
    0x08U, 0xa4U, 0x16U, 0x57U, 0xc1U, 0x6eU, 0xf4U, 0x68U, 0xb2U, 0x28U, 0xa8U, 0x27U, 0x9bU,
    0xe3U, 0x31U, 0xa7U, 0x03U, 0xc3U, 0x35U, 0x96U, 0xfdU, 0x15U, 0xc1U, 0x3bU, 0x1bU, 0x07U,
    0xf9U, 0xaaU, 0x1dU, 0x3bU, 0xeaU, 0x57U, 0x78U, 0x9cU, 0xa0U, 0x31U, 0xadU, 0x85U, 0xc7U,
    0xa7U, 0x1dU, 0xd7U, 0x03U, 0x54U, 0xecU, 0x63U, 0x12U, 0x38U, 0xcaU, 0x34U, 0x45U
  };

static uint8_t
test4_plaintext[112U] =
  {
    0x61U, 0x62U, 0x63U, 0x64U, 0x65U, 0x66U, 0x67U, 0x68U, 0x62U, 0x63U, 0x64U, 0x65U, 0x66U,
    0x67U, 0x68U, 0x69U, 0x63U, 0x64U, 0x65U, 0x66U, 0x67U, 0x68U, 0x69U, 0x6aU, 0x64U, 0x65U,
    0x66U, 0x67U, 0x68U, 0x69U, 0x6aU, 0x6bU, 0x65U, 0x66U, 0x67U, 0x68U, 0x69U, 0x6aU, 0x6bU,
    0x6cU, 0x66U, 0x67U, 0x68U, 0x69U, 0x6aU, 0x6bU, 0x6cU, 0x6dU, 0x67U, 0x68U, 0x69U, 0x6aU,
    0x6bU, 0x6cU, 0x6dU, 0x6eU, 0x68U, 0x69U, 0x6aU, 0x6bU, 0x6cU, 0x6dU, 0x6eU, 0x6fU, 0x69U,
    0x6aU, 0x6bU, 0x6cU, 0x6dU, 0x6eU, 0x6fU, 0x70U, 0x6aU, 0x6bU, 0x6cU, 0x6dU, 0x6eU, 0x6fU,
    0x70U, 0x71U, 0x6bU, 0x6cU, 0x6dU, 0x6eU, 0x6fU, 0x70U, 0x71U, 0x72U, 0x6cU, 0x6dU, 0x6eU,
    0x6fU, 0x70U, 0x71U, 0x72U, 0x73U, 0x6dU, 0x6eU, 0x6fU, 0x70U, 0x71U, 0x72U, 0x73U, 0x74U,
    0x6eU, 0x6fU, 0x70U, 0x71U, 0x72U, 0x73U, 0x74U, 0x75U
  };

static uint8_t
test4_expected_sha2_224[28U] =
  {
    0xc9U, 0x7cU, 0xa9U, 0xa5U, 0x59U, 0x85U, 0x0cU, 0xe9U, 0x7aU, 0x04U, 0xa9U, 0x6dU, 0xefU,
    0x6dU, 0x99U, 0xa9U, 0xe0U, 0xe0U, 0xe2U, 0xabU, 0x14U, 0xe6U, 0xb8U, 0xdfU, 0x26U, 0x5fU,
    0xc0U, 0xb3U
  };

static uint8_t
test4_expected_sha2_256[32U] =
  {
    0xcfU, 0x5bU, 0x16U, 0xa7U, 0x78U, 0xafU, 0x83U, 0x80U, 0x03U, 0x6cU, 0xe5U, 0x9eU, 0x7bU,
    0x04U, 0x92U, 0x37U, 0x0bU, 0x24U, 0x9bU, 0x11U, 0xe8U, 0xf0U, 0x7aU, 0x51U, 0xafU, 0xacU,
    0x45U, 0x03U, 0x7aU, 0xfeU, 0xe9U, 0xd1U
  };

static uint8_t
test4_expected_sha2_384[48U] =
  {
    0x09U, 0x33U, 0x0cU, 0x33U, 0xf7U, 0x11U, 0x47U, 0xe8U, 0x3dU, 0x19U, 0x2fU, 0xc7U, 0x82U,
    0xcdU, 0x1bU, 0x47U, 0x53U, 0x11U, 0x1bU, 0x17U, 0x3bU, 0x3bU, 0x05U, 0xd2U, 0x2fU, 0xa0U,
    0x80U, 0x86U, 0xe3U, 0xb0U, 0xf7U, 0x12U, 0xfcU, 0xc7U, 0xc7U, 0x1aU, 0x55U, 0x7eU, 0x2dU,
    0xb9U, 0x66U, 0xc3U, 0xe9U, 0xfaU, 0x91U, 0x74U, 0x60U, 0x39U
  };

static uint8_t
test4_expected_sha2_512[64U] =
  {
    0x8eU, 0x95U, 0x9bU, 0x75U, 0xdaU, 0xe3U, 0x13U, 0xdaU, 0x8cU, 0xf4U, 0xf7U, 0x28U, 0x14U,
    0xfcU, 0x14U, 0x3fU, 0x8fU, 0x77U, 0x79U, 0xc6U, 0xebU, 0x9fU, 0x7fU, 0xa1U, 0x72U, 0x99U,
    0xaeU, 0xadU, 0xb6U, 0x88U, 0x90U, 0x18U, 0x50U, 0x1dU, 0x28U, 0x9eU, 0x49U, 0x00U, 0xf7U,
    0xe4U, 0x33U, 0x1bU, 0x99U, 0xdeU, 0xc4U, 0xb5U, 0x43U, 0x3aU, 0xc7U, 0xd3U, 0x29U, 0xeeU,
    0xb6U, 0xddU, 0x26U, 0x54U, 0x5eU, 0x96U, 0xe5U, 0x5bU, 0x87U, 0x4bU, 0xe9U, 0x09U
  };

exit_code main(void)
{
  C_String_print("\nTEST 1. SHA2\n");
  test_sha2(3U,
    test1_plaintext,
    test1_expected_sha2_224,
    test1_expected_sha2_256,
    test1_expected_sha2_384,
    test1_expected_sha2_512);
  C_String_print("\nTEST 2. SHA2\n");
  test_sha2(0U,
    test2_plaintext,
    test2_expected_sha2_224,
    test2_expected_sha2_256,
    test2_expected_sha2_384,
    test2_expected_sha2_512);
  C_String_print("\nTEST 3. SHA2\n");
  test_sha2(56U,
    test3_plaintext,
    test3_expected_sha2_224,
    test3_expected_sha2_256,
    test3_expected_sha2_384,
    test3_expected_sha2_512);
  C_String_print("\nTEST 4. SHA2\n");
  test_sha2(112U,
    test4_plaintext,
    test4_expected_sha2_224,
    test4_expected_sha2_256,
    test4_expected_sha2_384,
    test4_expected_sha2_512);
  return EXIT_SUCCESS;
}

