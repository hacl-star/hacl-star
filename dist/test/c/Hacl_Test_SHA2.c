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
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
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
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (uint32_t));
  uint8_t *b10 = b;
  uint32_t u = load32_be(b10);
  ws[0U] = u;
  uint32_t u0 = load32_be(b10 + (uint32_t)4U);
  ws[1U] = u0;
  uint32_t u1 = load32_be(b10 + (uint32_t)8U);
  ws[2U] = u1;
  uint32_t u2 = load32_be(b10 + (uint32_t)12U);
  ws[3U] = u2;
  uint32_t u3 = load32_be(b10 + (uint32_t)16U);
  ws[4U] = u3;
  uint32_t u4 = load32_be(b10 + (uint32_t)20U);
  ws[5U] = u4;
  uint32_t u5 = load32_be(b10 + (uint32_t)24U);
  ws[6U] = u5;
  uint32_t u6 = load32_be(b10 + (uint32_t)28U);
  ws[7U] = u6;
  uint32_t u7 = load32_be(b10 + (uint32_t)32U);
  ws[8U] = u7;
  uint32_t u8 = load32_be(b10 + (uint32_t)36U);
  ws[9U] = u8;
  uint32_t u9 = load32_be(b10 + (uint32_t)40U);
  ws[10U] = u9;
  uint32_t u10 = load32_be(b10 + (uint32_t)44U);
  ws[11U] = u10;
  uint32_t u11 = load32_be(b10 + (uint32_t)48U);
  ws[12U] = u11;
  uint32_t u12 = load32_be(b10 + (uint32_t)52U);
  ws[13U] = u12;
  uint32_t u13 = load32_be(b10 + (uint32_t)56U);
  ws[14U] = u13;
  uint32_t u14 = load32_be(b10 + (uint32_t)60U);
  ws[15U] = u14;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint32_t k_t = Hacl_Impl_SHA2_Generic_k224_256[(uint32_t)16U * i0 + i];
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
        +
          ((e0 << (uint32_t)26U | e0 >> (uint32_t)6U)
          ^
            ((e0 << (uint32_t)21U | e0 >> (uint32_t)11U)
            ^ (e0 << (uint32_t)7U | e0 >> (uint32_t)25U)))
        + ((e0 & f0) ^ (~e0 & g0))
        + k_e_t
        + ws_t;
      uint32_t
      t2 =
        ((a0 << (uint32_t)30U | a0 >> (uint32_t)2U)
        ^
          ((a0 << (uint32_t)19U | a0 >> (uint32_t)13U)
          ^ (a0 << (uint32_t)10U | a0 >> (uint32_t)22U)))
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
    if (i0 < (uint32_t)3U)
    {
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint32_t t16 = ws[i];
        uint32_t t15 = ws[(i + (uint32_t)1U) % (uint32_t)16U];
        uint32_t t7 = ws[(i + (uint32_t)9U) % (uint32_t)16U];
        uint32_t t2 = ws[(i + (uint32_t)14U) % (uint32_t)16U];
        uint32_t
        s1 =
          (t2 << (uint32_t)15U | t2 >> (uint32_t)17U)
          ^ ((t2 << (uint32_t)13U | t2 >> (uint32_t)19U) ^ t2 >> (uint32_t)10U);
        uint32_t
        s0 =
          (t15 << (uint32_t)25U | t15 >> (uint32_t)7U)
          ^ ((t15 << (uint32_t)14U | t15 >> (uint32_t)18U) ^ t15 >> (uint32_t)3U);
        ws[i] = s1 + t7 + s0 + t16;
      }
    }
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t *os = hash;
    uint32_t x = hash[i] + hash_old[i];
    os[i] = x;
  }
}

static inline void sha256_update_nblocks(uint32_t len, uint8_t *b, uint32_t *st)
{
  uint32_t blocks = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks; i++)
  {
    uint8_t *b0 = b;
    uint8_t *mb = b0 + i * (uint32_t)64U;
    sha256_update(mb, st);
  }
}

static inline void
sha256_update_last(uint64_t totlen, uint32_t len, uint8_t *b, uint32_t *hash)
{
  uint32_t blocks;
  if (len + (uint32_t)8U + (uint32_t)1U <= (uint32_t)64U)
  {
    blocks = (uint32_t)1U;
  }
  else
  {
    blocks = (uint32_t)2U;
  }
  uint32_t fin = blocks * (uint32_t)64U;
  uint8_t last[128U] = { 0U };
  uint8_t totlen_buf[8U] = { 0U };
  uint64_t total_len_bits = totlen << (uint32_t)3U;
  store64_be(totlen_buf, total_len_bits);
  uint8_t *b0 = b;
  memcpy(last, b0, len * sizeof (uint8_t));
  last[len] = (uint8_t)0x80U;
  memcpy(last + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last00 = last;
  uint8_t *last10 = last + (uint32_t)64U;
  uint8_t *l0 = last00;
  uint8_t *l1 = last10;
  uint8_t *lb0 = l0;
  uint8_t *lb1 = l1;
  uint8_t *last0 = lb0;
  uint8_t *last1 = lb1;
  sha256_update(last0, hash);
  if (blocks > (uint32_t)1U)
  {
    sha256_update(last1, hash);
  }
}

static inline void sha256_finish(uint32_t *st, uint8_t *h)
{
  uint8_t hbuf[32U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    store32_be(hbuf + i * (uint32_t)4U, st[i]);
  }
  memcpy(h, hbuf, (uint32_t)32U * sizeof (uint8_t));
}

static inline void sha224_init(uint32_t *hash)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
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
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    store32_be(hbuf + i * (uint32_t)4U, st[i]);
  }
  memcpy(h, hbuf, (uint32_t)28U * sizeof (uint8_t));
}

static void sha512_init(uint64_t *hash)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
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
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (uint64_t));
  uint8_t *b10 = b;
  uint64_t u = load64_be(b10);
  ws[0U] = u;
  uint64_t u0 = load64_be(b10 + (uint32_t)8U);
  ws[1U] = u0;
  uint64_t u1 = load64_be(b10 + (uint32_t)16U);
  ws[2U] = u1;
  uint64_t u2 = load64_be(b10 + (uint32_t)24U);
  ws[3U] = u2;
  uint64_t u3 = load64_be(b10 + (uint32_t)32U);
  ws[4U] = u3;
  uint64_t u4 = load64_be(b10 + (uint32_t)40U);
  ws[5U] = u4;
  uint64_t u5 = load64_be(b10 + (uint32_t)48U);
  ws[6U] = u5;
  uint64_t u6 = load64_be(b10 + (uint32_t)56U);
  ws[7U] = u6;
  uint64_t u7 = load64_be(b10 + (uint32_t)64U);
  ws[8U] = u7;
  uint64_t u8 = load64_be(b10 + (uint32_t)72U);
  ws[9U] = u8;
  uint64_t u9 = load64_be(b10 + (uint32_t)80U);
  ws[10U] = u9;
  uint64_t u10 = load64_be(b10 + (uint32_t)88U);
  ws[11U] = u10;
  uint64_t u11 = load64_be(b10 + (uint32_t)96U);
  ws[12U] = u11;
  uint64_t u12 = load64_be(b10 + (uint32_t)104U);
  ws[13U] = u12;
  uint64_t u13 = load64_be(b10 + (uint32_t)112U);
  ws[14U] = u13;
  uint64_t u14 = load64_be(b10 + (uint32_t)120U);
  ws[15U] = u14;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)5U; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t k_t = Hacl_Impl_SHA2_Generic_k384_512[(uint32_t)16U * i0 + i];
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
        +
          ((e0 << (uint32_t)50U | e0 >> (uint32_t)14U)
          ^
            ((e0 << (uint32_t)46U | e0 >> (uint32_t)18U)
            ^ (e0 << (uint32_t)23U | e0 >> (uint32_t)41U)))
        + ((e0 & f0) ^ (~e0 & g0))
        + k_e_t
        + ws_t;
      uint64_t
      t2 =
        ((a0 << (uint32_t)36U | a0 >> (uint32_t)28U)
        ^
          ((a0 << (uint32_t)30U | a0 >> (uint32_t)34U)
          ^ (a0 << (uint32_t)25U | a0 >> (uint32_t)39U)))
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
    if (i0 < (uint32_t)4U)
    {
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint64_t t16 = ws[i];
        uint64_t t15 = ws[(i + (uint32_t)1U) % (uint32_t)16U];
        uint64_t t7 = ws[(i + (uint32_t)9U) % (uint32_t)16U];
        uint64_t t2 = ws[(i + (uint32_t)14U) % (uint32_t)16U];
        uint64_t
        s1 =
          (t2 << (uint32_t)45U | t2 >> (uint32_t)19U)
          ^ ((t2 << (uint32_t)3U | t2 >> (uint32_t)61U) ^ t2 >> (uint32_t)6U);
        uint64_t
        s0 =
          (t15 << (uint32_t)63U | t15 >> (uint32_t)1U)
          ^ ((t15 << (uint32_t)56U | t15 >> (uint32_t)8U) ^ t15 >> (uint32_t)7U);
        ws[i] = s1 + t7 + s0 + t16;
      }
    }
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t *os = hash;
    uint64_t x = hash[i] + hash_old[i];
    os[i] = x;
  }
}

static inline void sha512_update_nblocks(uint32_t len, uint8_t *b, uint64_t *st)
{
  uint32_t blocks = len / (uint32_t)128U;
  for (uint32_t i = (uint32_t)0U; i < blocks; i++)
  {
    uint8_t *b0 = b;
    uint8_t *mb = b0 + i * (uint32_t)128U;
    sha512_update(mb, st);
  }
}

static inline void
sha512_update_last(FStar_UInt128_uint128 totlen, uint32_t len, uint8_t *b, uint64_t *hash)
{
  uint32_t blocks;
  if (len + (uint32_t)16U + (uint32_t)1U <= (uint32_t)128U)
  {
    blocks = (uint32_t)1U;
  }
  else
  {
    blocks = (uint32_t)2U;
  }
  uint32_t fin = blocks * (uint32_t)128U;
  uint8_t last[256U] = { 0U };
  uint8_t totlen_buf[16U] = { 0U };
  FStar_UInt128_uint128 total_len_bits = FStar_UInt128_shift_left(totlen, (uint32_t)3U);
  store128_be(totlen_buf, total_len_bits);
  uint8_t *b0 = b;
  memcpy(last, b0, len * sizeof (uint8_t));
  last[len] = (uint8_t)0x80U;
  memcpy(last + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (uint8_t));
  uint8_t *last00 = last;
  uint8_t *last10 = last + (uint32_t)128U;
  uint8_t *l0 = last00;
  uint8_t *l1 = last10;
  uint8_t *lb0 = l0;
  uint8_t *lb1 = l1;
  uint8_t *last0 = lb0;
  uint8_t *last1 = lb1;
  sha512_update(last0, hash);
  if (blocks > (uint32_t)1U)
  {
    sha512_update(last1, hash);
  }
}

static inline void sha512_finish(uint64_t *st, uint8_t *h)
{
  uint8_t hbuf[64U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    store64_be(hbuf + i * (uint32_t)8U, st[i]);
  }
  memcpy(h, hbuf, (uint32_t)64U * sizeof (uint8_t));
}

static inline void sha384_init(uint64_t *hash)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
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
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    store64_be(hbuf + i * (uint32_t)8U, st[i]);
  }
  memcpy(h, hbuf, (uint32_t)48U * sizeof (uint8_t));
}

/**
Hash `input`, of len `input_len`, into `dst`, an array of 32 bytes.
*/
static void hash_256(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint8_t *ib = input;
  uint8_t *rb = dst;
  uint32_t st[8U] = { 0U };
  sha256_init(st);
  uint32_t rem = input_len % (uint32_t)64U;
  uint64_t len_ = (uint64_t)input_len;
  sha256_update_nblocks(input_len, ib, st);
  uint32_t rem1 = input_len % (uint32_t)64U;
  uint8_t *b0 = ib;
  uint8_t *lb = b0 + input_len - rem1;
  sha256_update_last(len_, rem, lb, st);
  sha256_finish(st, rb);
}

/**
Hash `input`, of len `input_len`, into `dst`, an array of 28 bytes.
*/
static void hash_224(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint8_t *ib = input;
  uint8_t *rb = dst;
  uint32_t st[8U] = { 0U };
  sha224_init(st);
  uint32_t rem = input_len % (uint32_t)64U;
  uint64_t len_ = (uint64_t)input_len;
  sha224_update_nblocks(input_len, ib, st);
  uint32_t rem1 = input_len % (uint32_t)64U;
  uint8_t *b0 = ib;
  uint8_t *lb = b0 + input_len - rem1;
  sha224_update_last(len_, rem, lb, st);
  sha224_finish(st, rb);
}

/**
Hash `input`, of len `input_len`, into `dst`, an array of 64 bytes.
*/
static void hash_512(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint8_t *ib = input;
  uint8_t *rb = dst;
  uint64_t st[8U] = { 0U };
  sha512_init(st);
  uint32_t rem = input_len % (uint32_t)128U;
  FStar_UInt128_uint128 len_ = FStar_UInt128_uint64_to_uint128((uint64_t)input_len);
  sha512_update_nblocks(input_len, ib, st);
  uint32_t rem1 = input_len % (uint32_t)128U;
  uint8_t *b0 = ib;
  uint8_t *lb = b0 + input_len - rem1;
  sha512_update_last(len_, rem, lb, st);
  sha512_finish(st, rb);
}

/**
Hash `input`, of len `input_len`, into `dst`, an array of 48 bytes.
*/
static void hash_384(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint8_t *ib = input;
  uint8_t *rb = dst;
  uint64_t st[8U] = { 0U };
  sha384_init(st);
  uint32_t rem = input_len % (uint32_t)128U;
  FStar_UInt128_uint128 len_ = FStar_UInt128_uint64_to_uint128((uint64_t)input_len);
  sha384_update_nblocks(input_len, ib, st);
  uint32_t rem1 = input_len % (uint32_t)128U;
  uint8_t *b0 = ib;
  uint8_t *lb = b0 + input_len - rem1;
  sha384_update_last(len_, rem, lb, st);
  sha384_finish(st, rb);
}

extern void C_String_print(C_String_t uu___);

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
  hash_224(msg, msg_len, test224);
  hash_256(msg, msg_len, test256);
  hash_384(msg, msg_len, test384);
  hash_512(msg, msg_len, test512);
  if (!Lib_PrintBuffer_result_compare_display((uint32_t)28U, test224, expected224))
  {
    exit((int32_t)255);
  }
  if (!Lib_PrintBuffer_result_compare_display((uint32_t)32U, test256, expected256))
  {
    exit((int32_t)255);
  }
  if (!Lib_PrintBuffer_result_compare_display((uint32_t)48U, test384, expected384))
  {
    exit((int32_t)255);
  }
  if (!Lib_PrintBuffer_result_compare_display((uint32_t)64U, test512, expected512))
  {
    exit((int32_t)255);
  }
}

static uint8_t test1_plaintext[3U] = { (uint8_t)0x61U, (uint8_t)0x62U, (uint8_t)0x63U };

static uint8_t
test1_expected_sha2_224[28U] =
  {
    (uint8_t)0x23U, (uint8_t)0x09U, (uint8_t)0x7dU, (uint8_t)0x22U, (uint8_t)0x34U, (uint8_t)0x05U,
    (uint8_t)0xd8U, (uint8_t)0x22U, (uint8_t)0x86U, (uint8_t)0x42U, (uint8_t)0xa4U, (uint8_t)0x77U,
    (uint8_t)0xbdU, (uint8_t)0xa2U, (uint8_t)0x55U, (uint8_t)0xb3U, (uint8_t)0x2aU, (uint8_t)0xadU,
    (uint8_t)0xbcU, (uint8_t)0xe4U, (uint8_t)0xbdU, (uint8_t)0xa0U, (uint8_t)0xb3U, (uint8_t)0xf7U,
    (uint8_t)0xe3U, (uint8_t)0x6cU, (uint8_t)0x9dU, (uint8_t)0xa7U
  };

static uint8_t
test1_expected_sha2_256[32U] =
  {
    (uint8_t)0xbaU, (uint8_t)0x78U, (uint8_t)0x16U, (uint8_t)0xbfU, (uint8_t)0x8fU, (uint8_t)0x01U,
    (uint8_t)0xcfU, (uint8_t)0xeaU, (uint8_t)0x41U, (uint8_t)0x41U, (uint8_t)0x40U, (uint8_t)0xdeU,
    (uint8_t)0x5dU, (uint8_t)0xaeU, (uint8_t)0x22U, (uint8_t)0x23U, (uint8_t)0xb0U, (uint8_t)0x03U,
    (uint8_t)0x61U, (uint8_t)0xa3U, (uint8_t)0x96U, (uint8_t)0x17U, (uint8_t)0x7aU, (uint8_t)0x9cU,
    (uint8_t)0xb4U, (uint8_t)0x10U, (uint8_t)0xffU, (uint8_t)0x61U, (uint8_t)0xf2U, (uint8_t)0x00U,
    (uint8_t)0x15U, (uint8_t)0xadU
  };

static uint8_t
test1_expected_sha2_384[48U] =
  {
    (uint8_t)0xcbU, (uint8_t)0x00U, (uint8_t)0x75U, (uint8_t)0x3fU, (uint8_t)0x45U, (uint8_t)0xa3U,
    (uint8_t)0x5eU, (uint8_t)0x8bU, (uint8_t)0xb5U, (uint8_t)0xa0U, (uint8_t)0x3dU, (uint8_t)0x69U,
    (uint8_t)0x9aU, (uint8_t)0xc6U, (uint8_t)0x50U, (uint8_t)0x07U, (uint8_t)0x27U, (uint8_t)0x2cU,
    (uint8_t)0x32U, (uint8_t)0xabU, (uint8_t)0x0eU, (uint8_t)0xdeU, (uint8_t)0xd1U, (uint8_t)0x63U,
    (uint8_t)0x1aU, (uint8_t)0x8bU, (uint8_t)0x60U, (uint8_t)0x5aU, (uint8_t)0x43U, (uint8_t)0xffU,
    (uint8_t)0x5bU, (uint8_t)0xedU, (uint8_t)0x80U, (uint8_t)0x86U, (uint8_t)0x07U, (uint8_t)0x2bU,
    (uint8_t)0xa1U, (uint8_t)0xe7U, (uint8_t)0xccU, (uint8_t)0x23U, (uint8_t)0x58U, (uint8_t)0xbaU,
    (uint8_t)0xecU, (uint8_t)0xa1U, (uint8_t)0x34U, (uint8_t)0xc8U, (uint8_t)0x25U, (uint8_t)0xa7U
  };

static uint8_t
test1_expected_sha2_512[64U] =
  {
    (uint8_t)0xddU, (uint8_t)0xafU, (uint8_t)0x35U, (uint8_t)0xa1U, (uint8_t)0x93U, (uint8_t)0x61U,
    (uint8_t)0x7aU, (uint8_t)0xbaU, (uint8_t)0xccU, (uint8_t)0x41U, (uint8_t)0x73U, (uint8_t)0x49U,
    (uint8_t)0xaeU, (uint8_t)0x20U, (uint8_t)0x41U, (uint8_t)0x31U, (uint8_t)0x12U, (uint8_t)0xe6U,
    (uint8_t)0xfaU, (uint8_t)0x4eU, (uint8_t)0x89U, (uint8_t)0xa9U, (uint8_t)0x7eU, (uint8_t)0xa2U,
    (uint8_t)0x0aU, (uint8_t)0x9eU, (uint8_t)0xeeU, (uint8_t)0xe6U, (uint8_t)0x4bU, (uint8_t)0x55U,
    (uint8_t)0xd3U, (uint8_t)0x9aU, (uint8_t)0x21U, (uint8_t)0x92U, (uint8_t)0x99U, (uint8_t)0x2aU,
    (uint8_t)0x27U, (uint8_t)0x4fU, (uint8_t)0xc1U, (uint8_t)0xa8U, (uint8_t)0x36U, (uint8_t)0xbaU,
    (uint8_t)0x3cU, (uint8_t)0x23U, (uint8_t)0xa3U, (uint8_t)0xfeU, (uint8_t)0xebU, (uint8_t)0xbdU,
    (uint8_t)0x45U, (uint8_t)0x4dU, (uint8_t)0x44U, (uint8_t)0x23U, (uint8_t)0x64U, (uint8_t)0x3cU,
    (uint8_t)0xe8U, (uint8_t)0x0eU, (uint8_t)0x2aU, (uint8_t)0x9aU, (uint8_t)0xc9U, (uint8_t)0x4fU,
    (uint8_t)0xa5U, (uint8_t)0x4cU, (uint8_t)0xa4U, (uint8_t)0x9fU
  };

static uint8_t test2_plaintext[0U] = {  };

static uint8_t
test2_expected_sha2_224[28U] =
  {
    (uint8_t)0xd1U, (uint8_t)0x4aU, (uint8_t)0x02U, (uint8_t)0x8cU, (uint8_t)0x2aU, (uint8_t)0x3aU,
    (uint8_t)0x2bU, (uint8_t)0xc9U, (uint8_t)0x47U, (uint8_t)0x61U, (uint8_t)0x02U, (uint8_t)0xbbU,
    (uint8_t)0x28U, (uint8_t)0x82U, (uint8_t)0x34U, (uint8_t)0xc4U, (uint8_t)0x15U, (uint8_t)0xa2U,
    (uint8_t)0xb0U, (uint8_t)0x1fU, (uint8_t)0x82U, (uint8_t)0x8eU, (uint8_t)0xa6U, (uint8_t)0x2aU,
    (uint8_t)0xc5U, (uint8_t)0xb3U, (uint8_t)0xe4U, (uint8_t)0x2fU
  };

static uint8_t
test2_expected_sha2_256[32U] =
  {
    (uint8_t)0xe3U, (uint8_t)0xb0U, (uint8_t)0xc4U, (uint8_t)0x42U, (uint8_t)0x98U, (uint8_t)0xfcU,
    (uint8_t)0x1cU, (uint8_t)0x14U, (uint8_t)0x9aU, (uint8_t)0xfbU, (uint8_t)0xf4U, (uint8_t)0xc8U,
    (uint8_t)0x99U, (uint8_t)0x6fU, (uint8_t)0xb9U, (uint8_t)0x24U, (uint8_t)0x27U, (uint8_t)0xaeU,
    (uint8_t)0x41U, (uint8_t)0xe4U, (uint8_t)0x64U, (uint8_t)0x9bU, (uint8_t)0x93U, (uint8_t)0x4cU,
    (uint8_t)0xa4U, (uint8_t)0x95U, (uint8_t)0x99U, (uint8_t)0x1bU, (uint8_t)0x78U, (uint8_t)0x52U,
    (uint8_t)0xb8U, (uint8_t)0x55U
  };

static uint8_t
test2_expected_sha2_384[48U] =
  {
    (uint8_t)0x38U, (uint8_t)0xb0U, (uint8_t)0x60U, (uint8_t)0xa7U, (uint8_t)0x51U, (uint8_t)0xacU,
    (uint8_t)0x96U, (uint8_t)0x38U, (uint8_t)0x4cU, (uint8_t)0xd9U, (uint8_t)0x32U, (uint8_t)0x7eU,
    (uint8_t)0xb1U, (uint8_t)0xb1U, (uint8_t)0xe3U, (uint8_t)0x6aU, (uint8_t)0x21U, (uint8_t)0xfdU,
    (uint8_t)0xb7U, (uint8_t)0x11U, (uint8_t)0x14U, (uint8_t)0xbeU, (uint8_t)0x07U, (uint8_t)0x43U,
    (uint8_t)0x4cU, (uint8_t)0x0cU, (uint8_t)0xc7U, (uint8_t)0xbfU, (uint8_t)0x63U, (uint8_t)0xf6U,
    (uint8_t)0xe1U, (uint8_t)0xdaU, (uint8_t)0x27U, (uint8_t)0x4eU, (uint8_t)0xdeU, (uint8_t)0xbfU,
    (uint8_t)0xe7U, (uint8_t)0x6fU, (uint8_t)0x65U, (uint8_t)0xfbU, (uint8_t)0xd5U, (uint8_t)0x1aU,
    (uint8_t)0xd2U, (uint8_t)0xf1U, (uint8_t)0x48U, (uint8_t)0x98U, (uint8_t)0xb9U, (uint8_t)0x5bU
  };

static uint8_t
test2_expected_sha2_512[64U] =
  {
    (uint8_t)0xcfU, (uint8_t)0x83U, (uint8_t)0xe1U, (uint8_t)0x35U, (uint8_t)0x7eU, (uint8_t)0xefU,
    (uint8_t)0xb8U, (uint8_t)0xbdU, (uint8_t)0xf1U, (uint8_t)0x54U, (uint8_t)0x28U, (uint8_t)0x50U,
    (uint8_t)0xd6U, (uint8_t)0x6dU, (uint8_t)0x80U, (uint8_t)0x07U, (uint8_t)0xd6U, (uint8_t)0x20U,
    (uint8_t)0xe4U, (uint8_t)0x05U, (uint8_t)0x0bU, (uint8_t)0x57U, (uint8_t)0x15U, (uint8_t)0xdcU,
    (uint8_t)0x83U, (uint8_t)0xf4U, (uint8_t)0xa9U, (uint8_t)0x21U, (uint8_t)0xd3U, (uint8_t)0x6cU,
    (uint8_t)0xe9U, (uint8_t)0xceU, (uint8_t)0x47U, (uint8_t)0xd0U, (uint8_t)0xd1U, (uint8_t)0x3cU,
    (uint8_t)0x5dU, (uint8_t)0x85U, (uint8_t)0xf2U, (uint8_t)0xb0U, (uint8_t)0xffU, (uint8_t)0x83U,
    (uint8_t)0x18U, (uint8_t)0xd2U, (uint8_t)0x87U, (uint8_t)0x7eU, (uint8_t)0xecU, (uint8_t)0x2fU,
    (uint8_t)0x63U, (uint8_t)0xb9U, (uint8_t)0x31U, (uint8_t)0xbdU, (uint8_t)0x47U, (uint8_t)0x41U,
    (uint8_t)0x7aU, (uint8_t)0x81U, (uint8_t)0xa5U, (uint8_t)0x38U, (uint8_t)0x32U, (uint8_t)0x7aU,
    (uint8_t)0xf9U, (uint8_t)0x27U, (uint8_t)0xdaU, (uint8_t)0x3eU
  };

static uint8_t
test3_plaintext[56U] =
  {
    (uint8_t)0x61U, (uint8_t)0x62U, (uint8_t)0x63U, (uint8_t)0x64U, (uint8_t)0x62U, (uint8_t)0x63U,
    (uint8_t)0x64U, (uint8_t)0x65U, (uint8_t)0x63U, (uint8_t)0x64U, (uint8_t)0x65U, (uint8_t)0x66U,
    (uint8_t)0x64U, (uint8_t)0x65U, (uint8_t)0x66U, (uint8_t)0x67U, (uint8_t)0x65U, (uint8_t)0x66U,
    (uint8_t)0x67U, (uint8_t)0x68U, (uint8_t)0x66U, (uint8_t)0x67U, (uint8_t)0x68U, (uint8_t)0x69U,
    (uint8_t)0x67U, (uint8_t)0x68U, (uint8_t)0x69U, (uint8_t)0x6aU, (uint8_t)0x68U, (uint8_t)0x69U,
    (uint8_t)0x6aU, (uint8_t)0x6bU, (uint8_t)0x69U, (uint8_t)0x6aU, (uint8_t)0x6bU, (uint8_t)0x6cU,
    (uint8_t)0x6aU, (uint8_t)0x6bU, (uint8_t)0x6cU, (uint8_t)0x6dU, (uint8_t)0x6bU, (uint8_t)0x6cU,
    (uint8_t)0x6dU, (uint8_t)0x6eU, (uint8_t)0x6cU, (uint8_t)0x6dU, (uint8_t)0x6eU, (uint8_t)0x6fU,
    (uint8_t)0x6dU, (uint8_t)0x6eU, (uint8_t)0x6fU, (uint8_t)0x70U, (uint8_t)0x6eU, (uint8_t)0x6fU,
    (uint8_t)0x70U, (uint8_t)0x71U
  };

static uint8_t
test3_expected_sha2_224[28U] =
  {
    (uint8_t)0x75U, (uint8_t)0x38U, (uint8_t)0x8bU, (uint8_t)0x16U, (uint8_t)0x51U, (uint8_t)0x27U,
    (uint8_t)0x76U, (uint8_t)0xccU, (uint8_t)0x5dU, (uint8_t)0xbaU, (uint8_t)0x5dU, (uint8_t)0xa1U,
    (uint8_t)0xfdU, (uint8_t)0x89U, (uint8_t)0x01U, (uint8_t)0x50U, (uint8_t)0xb0U, (uint8_t)0xc6U,
    (uint8_t)0x45U, (uint8_t)0x5cU, (uint8_t)0xb4U, (uint8_t)0xf5U, (uint8_t)0x8bU, (uint8_t)0x19U,
    (uint8_t)0x52U, (uint8_t)0x52U, (uint8_t)0x25U, (uint8_t)0x25U
  };

static uint8_t
test3_expected_sha2_256[32U] =
  {
    (uint8_t)0x24U, (uint8_t)0x8dU, (uint8_t)0x6aU, (uint8_t)0x61U, (uint8_t)0xd2U, (uint8_t)0x06U,
    (uint8_t)0x38U, (uint8_t)0xb8U, (uint8_t)0xe5U, (uint8_t)0xc0U, (uint8_t)0x26U, (uint8_t)0x93U,
    (uint8_t)0x0cU, (uint8_t)0x3eU, (uint8_t)0x60U, (uint8_t)0x39U, (uint8_t)0xa3U, (uint8_t)0x3cU,
    (uint8_t)0xe4U, (uint8_t)0x59U, (uint8_t)0x64U, (uint8_t)0xffU, (uint8_t)0x21U, (uint8_t)0x67U,
    (uint8_t)0xf6U, (uint8_t)0xecU, (uint8_t)0xedU, (uint8_t)0xd4U, (uint8_t)0x19U, (uint8_t)0xdbU,
    (uint8_t)0x06U, (uint8_t)0xc1U
  };

static uint8_t
test3_expected_sha2_384[48U] =
  {
    (uint8_t)0x33U, (uint8_t)0x91U, (uint8_t)0xfdU, (uint8_t)0xddU, (uint8_t)0xfcU, (uint8_t)0x8dU,
    (uint8_t)0xc7U, (uint8_t)0x39U, (uint8_t)0x37U, (uint8_t)0x07U, (uint8_t)0xa6U, (uint8_t)0x5bU,
    (uint8_t)0x1bU, (uint8_t)0x47U, (uint8_t)0x09U, (uint8_t)0x39U, (uint8_t)0x7cU, (uint8_t)0xf8U,
    (uint8_t)0xb1U, (uint8_t)0xd1U, (uint8_t)0x62U, (uint8_t)0xafU, (uint8_t)0x05U, (uint8_t)0xabU,
    (uint8_t)0xfeU, (uint8_t)0x8fU, (uint8_t)0x45U, (uint8_t)0x0dU, (uint8_t)0xe5U, (uint8_t)0xf3U,
    (uint8_t)0x6bU, (uint8_t)0xc6U, (uint8_t)0xb0U, (uint8_t)0x45U, (uint8_t)0x5aU, (uint8_t)0x85U,
    (uint8_t)0x20U, (uint8_t)0xbcU, (uint8_t)0x4eU, (uint8_t)0x6fU, (uint8_t)0x5fU, (uint8_t)0xe9U,
    (uint8_t)0x5bU, (uint8_t)0x1fU, (uint8_t)0xe3U, (uint8_t)0xc8U, (uint8_t)0x45U, (uint8_t)0x2bU
  };

static uint8_t
test3_expected_sha2_512[64U] =
  {
    (uint8_t)0x20U, (uint8_t)0x4aU, (uint8_t)0x8fU, (uint8_t)0xc6U, (uint8_t)0xddU, (uint8_t)0xa8U,
    (uint8_t)0x2fU, (uint8_t)0x0aU, (uint8_t)0x0cU, (uint8_t)0xedU, (uint8_t)0x7bU, (uint8_t)0xebU,
    (uint8_t)0x8eU, (uint8_t)0x08U, (uint8_t)0xa4U, (uint8_t)0x16U, (uint8_t)0x57U, (uint8_t)0xc1U,
    (uint8_t)0x6eU, (uint8_t)0xf4U, (uint8_t)0x68U, (uint8_t)0xb2U, (uint8_t)0x28U, (uint8_t)0xa8U,
    (uint8_t)0x27U, (uint8_t)0x9bU, (uint8_t)0xe3U, (uint8_t)0x31U, (uint8_t)0xa7U, (uint8_t)0x03U,
    (uint8_t)0xc3U, (uint8_t)0x35U, (uint8_t)0x96U, (uint8_t)0xfdU, (uint8_t)0x15U, (uint8_t)0xc1U,
    (uint8_t)0x3bU, (uint8_t)0x1bU, (uint8_t)0x07U, (uint8_t)0xf9U, (uint8_t)0xaaU, (uint8_t)0x1dU,
    (uint8_t)0x3bU, (uint8_t)0xeaU, (uint8_t)0x57U, (uint8_t)0x78U, (uint8_t)0x9cU, (uint8_t)0xa0U,
    (uint8_t)0x31U, (uint8_t)0xadU, (uint8_t)0x85U, (uint8_t)0xc7U, (uint8_t)0xa7U, (uint8_t)0x1dU,
    (uint8_t)0xd7U, (uint8_t)0x03U, (uint8_t)0x54U, (uint8_t)0xecU, (uint8_t)0x63U, (uint8_t)0x12U,
    (uint8_t)0x38U, (uint8_t)0xcaU, (uint8_t)0x34U, (uint8_t)0x45U
  };

static uint8_t
test4_plaintext[112U] =
  {
    (uint8_t)0x61U, (uint8_t)0x62U, (uint8_t)0x63U, (uint8_t)0x64U, (uint8_t)0x65U, (uint8_t)0x66U,
    (uint8_t)0x67U, (uint8_t)0x68U, (uint8_t)0x62U, (uint8_t)0x63U, (uint8_t)0x64U, (uint8_t)0x65U,
    (uint8_t)0x66U, (uint8_t)0x67U, (uint8_t)0x68U, (uint8_t)0x69U, (uint8_t)0x63U, (uint8_t)0x64U,
    (uint8_t)0x65U, (uint8_t)0x66U, (uint8_t)0x67U, (uint8_t)0x68U, (uint8_t)0x69U, (uint8_t)0x6aU,
    (uint8_t)0x64U, (uint8_t)0x65U, (uint8_t)0x66U, (uint8_t)0x67U, (uint8_t)0x68U, (uint8_t)0x69U,
    (uint8_t)0x6aU, (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x66U, (uint8_t)0x67U, (uint8_t)0x68U,
    (uint8_t)0x69U, (uint8_t)0x6aU, (uint8_t)0x6bU, (uint8_t)0x6cU, (uint8_t)0x66U, (uint8_t)0x67U,
    (uint8_t)0x68U, (uint8_t)0x69U, (uint8_t)0x6aU, (uint8_t)0x6bU, (uint8_t)0x6cU, (uint8_t)0x6dU,
    (uint8_t)0x67U, (uint8_t)0x68U, (uint8_t)0x69U, (uint8_t)0x6aU, (uint8_t)0x6bU, (uint8_t)0x6cU,
    (uint8_t)0x6dU, (uint8_t)0x6eU, (uint8_t)0x68U, (uint8_t)0x69U, (uint8_t)0x6aU, (uint8_t)0x6bU,
    (uint8_t)0x6cU, (uint8_t)0x6dU, (uint8_t)0x6eU, (uint8_t)0x6fU, (uint8_t)0x69U, (uint8_t)0x6aU,
    (uint8_t)0x6bU, (uint8_t)0x6cU, (uint8_t)0x6dU, (uint8_t)0x6eU, (uint8_t)0x6fU, (uint8_t)0x70U,
    (uint8_t)0x6aU, (uint8_t)0x6bU, (uint8_t)0x6cU, (uint8_t)0x6dU, (uint8_t)0x6eU, (uint8_t)0x6fU,
    (uint8_t)0x70U, (uint8_t)0x71U, (uint8_t)0x6bU, (uint8_t)0x6cU, (uint8_t)0x6dU, (uint8_t)0x6eU,
    (uint8_t)0x6fU, (uint8_t)0x70U, (uint8_t)0x71U, (uint8_t)0x72U, (uint8_t)0x6cU, (uint8_t)0x6dU,
    (uint8_t)0x6eU, (uint8_t)0x6fU, (uint8_t)0x70U, (uint8_t)0x71U, (uint8_t)0x72U, (uint8_t)0x73U,
    (uint8_t)0x6dU, (uint8_t)0x6eU, (uint8_t)0x6fU, (uint8_t)0x70U, (uint8_t)0x71U, (uint8_t)0x72U,
    (uint8_t)0x73U, (uint8_t)0x74U, (uint8_t)0x6eU, (uint8_t)0x6fU, (uint8_t)0x70U, (uint8_t)0x71U,
    (uint8_t)0x72U, (uint8_t)0x73U, (uint8_t)0x74U, (uint8_t)0x75U
  };

static uint8_t
test4_expected_sha2_224[28U] =
  {
    (uint8_t)0xc9U, (uint8_t)0x7cU, (uint8_t)0xa9U, (uint8_t)0xa5U, (uint8_t)0x59U, (uint8_t)0x85U,
    (uint8_t)0x0cU, (uint8_t)0xe9U, (uint8_t)0x7aU, (uint8_t)0x04U, (uint8_t)0xa9U, (uint8_t)0x6dU,
    (uint8_t)0xefU, (uint8_t)0x6dU, (uint8_t)0x99U, (uint8_t)0xa9U, (uint8_t)0xe0U, (uint8_t)0xe0U,
    (uint8_t)0xe2U, (uint8_t)0xabU, (uint8_t)0x14U, (uint8_t)0xe6U, (uint8_t)0xb8U, (uint8_t)0xdfU,
    (uint8_t)0x26U, (uint8_t)0x5fU, (uint8_t)0xc0U, (uint8_t)0xb3U
  };

static uint8_t
test4_expected_sha2_256[32U] =
  {
    (uint8_t)0xcfU, (uint8_t)0x5bU, (uint8_t)0x16U, (uint8_t)0xa7U, (uint8_t)0x78U, (uint8_t)0xafU,
    (uint8_t)0x83U, (uint8_t)0x80U, (uint8_t)0x03U, (uint8_t)0x6cU, (uint8_t)0xe5U, (uint8_t)0x9eU,
    (uint8_t)0x7bU, (uint8_t)0x04U, (uint8_t)0x92U, (uint8_t)0x37U, (uint8_t)0x0bU, (uint8_t)0x24U,
    (uint8_t)0x9bU, (uint8_t)0x11U, (uint8_t)0xe8U, (uint8_t)0xf0U, (uint8_t)0x7aU, (uint8_t)0x51U,
    (uint8_t)0xafU, (uint8_t)0xacU, (uint8_t)0x45U, (uint8_t)0x03U, (uint8_t)0x7aU, (uint8_t)0xfeU,
    (uint8_t)0xe9U, (uint8_t)0xd1U
  };

static uint8_t
test4_expected_sha2_384[48U] =
  {
    (uint8_t)0x09U, (uint8_t)0x33U, (uint8_t)0x0cU, (uint8_t)0x33U, (uint8_t)0xf7U, (uint8_t)0x11U,
    (uint8_t)0x47U, (uint8_t)0xe8U, (uint8_t)0x3dU, (uint8_t)0x19U, (uint8_t)0x2fU, (uint8_t)0xc7U,
    (uint8_t)0x82U, (uint8_t)0xcdU, (uint8_t)0x1bU, (uint8_t)0x47U, (uint8_t)0x53U, (uint8_t)0x11U,
    (uint8_t)0x1bU, (uint8_t)0x17U, (uint8_t)0x3bU, (uint8_t)0x3bU, (uint8_t)0x05U, (uint8_t)0xd2U,
    (uint8_t)0x2fU, (uint8_t)0xa0U, (uint8_t)0x80U, (uint8_t)0x86U, (uint8_t)0xe3U, (uint8_t)0xb0U,
    (uint8_t)0xf7U, (uint8_t)0x12U, (uint8_t)0xfcU, (uint8_t)0xc7U, (uint8_t)0xc7U, (uint8_t)0x1aU,
    (uint8_t)0x55U, (uint8_t)0x7eU, (uint8_t)0x2dU, (uint8_t)0xb9U, (uint8_t)0x66U, (uint8_t)0xc3U,
    (uint8_t)0xe9U, (uint8_t)0xfaU, (uint8_t)0x91U, (uint8_t)0x74U, (uint8_t)0x60U, (uint8_t)0x39U
  };

static uint8_t
test4_expected_sha2_512[64U] =
  {
    (uint8_t)0x8eU, (uint8_t)0x95U, (uint8_t)0x9bU, (uint8_t)0x75U, (uint8_t)0xdaU, (uint8_t)0xe3U,
    (uint8_t)0x13U, (uint8_t)0xdaU, (uint8_t)0x8cU, (uint8_t)0xf4U, (uint8_t)0xf7U, (uint8_t)0x28U,
    (uint8_t)0x14U, (uint8_t)0xfcU, (uint8_t)0x14U, (uint8_t)0x3fU, (uint8_t)0x8fU, (uint8_t)0x77U,
    (uint8_t)0x79U, (uint8_t)0xc6U, (uint8_t)0xebU, (uint8_t)0x9fU, (uint8_t)0x7fU, (uint8_t)0xa1U,
    (uint8_t)0x72U, (uint8_t)0x99U, (uint8_t)0xaeU, (uint8_t)0xadU, (uint8_t)0xb6U, (uint8_t)0x88U,
    (uint8_t)0x90U, (uint8_t)0x18U, (uint8_t)0x50U, (uint8_t)0x1dU, (uint8_t)0x28U, (uint8_t)0x9eU,
    (uint8_t)0x49U, (uint8_t)0x00U, (uint8_t)0xf7U, (uint8_t)0xe4U, (uint8_t)0x33U, (uint8_t)0x1bU,
    (uint8_t)0x99U, (uint8_t)0xdeU, (uint8_t)0xc4U, (uint8_t)0xb5U, (uint8_t)0x43U, (uint8_t)0x3aU,
    (uint8_t)0xc7U, (uint8_t)0xd3U, (uint8_t)0x29U, (uint8_t)0xeeU, (uint8_t)0xb6U, (uint8_t)0xddU,
    (uint8_t)0x26U, (uint8_t)0x54U, (uint8_t)0x5eU, (uint8_t)0x96U, (uint8_t)0xe5U, (uint8_t)0x5bU,
    (uint8_t)0x87U, (uint8_t)0x4bU, (uint8_t)0xe9U, (uint8_t)0x09U
  };

exit_code main(void)
{
  C_String_print("\nTEST 1. SHA2\n");
  test_sha2((uint32_t)3U,
    test1_plaintext,
    test1_expected_sha2_224,
    test1_expected_sha2_256,
    test1_expected_sha2_384,
    test1_expected_sha2_512);
  C_String_print("\nTEST 2. SHA2\n");
  test_sha2((uint32_t)0U,
    test2_plaintext,
    test2_expected_sha2_224,
    test2_expected_sha2_256,
    test2_expected_sha2_384,
    test2_expected_sha2_512);
  C_String_print("\nTEST 3. SHA2\n");
  test_sha2((uint32_t)56U,
    test3_plaintext,
    test3_expected_sha2_224,
    test3_expected_sha2_256,
    test3_expected_sha2_384,
    test3_expected_sha2_512);
  C_String_print("\nTEST 4. SHA2\n");
  test_sha2((uint32_t)112U,
    test4_plaintext,
    test4_expected_sha2_224,
    test4_expected_sha2_256,
    test4_expected_sha2_384,
    test4_expected_sha2_512);
  return EXIT_SUCCESS;
}

