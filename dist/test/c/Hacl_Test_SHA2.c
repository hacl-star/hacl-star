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


#include "Hacl_Test_SHA2.h"



static uint32_t
k224_256[64U] =
  {
    (uint32_t)0x428a2f98U, (uint32_t)0x71374491U, (uint32_t)0xb5c0fbcfU, (uint32_t)0xe9b5dba5U,
    (uint32_t)0x3956c25bU, (uint32_t)0x59f111f1U, (uint32_t)0x923f82a4U, (uint32_t)0xab1c5ed5U,
    (uint32_t)0xd807aa98U, (uint32_t)0x12835b01U, (uint32_t)0x243185beU, (uint32_t)0x550c7dc3U,
    (uint32_t)0x72be5d74U, (uint32_t)0x80deb1feU, (uint32_t)0x9bdc06a7U, (uint32_t)0xc19bf174U,
    (uint32_t)0xe49b69c1U, (uint32_t)0xefbe4786U, (uint32_t)0x0fc19dc6U, (uint32_t)0x240ca1ccU,
    (uint32_t)0x2de92c6fU, (uint32_t)0x4a7484aaU, (uint32_t)0x5cb0a9dcU, (uint32_t)0x76f988daU,
    (uint32_t)0x983e5152U, (uint32_t)0xa831c66dU, (uint32_t)0xb00327c8U, (uint32_t)0xbf597fc7U,
    (uint32_t)0xc6e00bf3U, (uint32_t)0xd5a79147U, (uint32_t)0x06ca6351U, (uint32_t)0x14292967U,
    (uint32_t)0x27b70a85U, (uint32_t)0x2e1b2138U, (uint32_t)0x4d2c6dfcU, (uint32_t)0x53380d13U,
    (uint32_t)0x650a7354U, (uint32_t)0x766a0abbU, (uint32_t)0x81c2c92eU, (uint32_t)0x92722c85U,
    (uint32_t)0xa2bfe8a1U, (uint32_t)0xa81a664bU, (uint32_t)0xc24b8b70U, (uint32_t)0xc76c51a3U,
    (uint32_t)0xd192e819U, (uint32_t)0xd6990624U, (uint32_t)0xf40e3585U, (uint32_t)0x106aa070U,
    (uint32_t)0x19a4c116U, (uint32_t)0x1e376c08U, (uint32_t)0x2748774cU, (uint32_t)0x34b0bcb5U,
    (uint32_t)0x391c0cb3U, (uint32_t)0x4ed8aa4aU, (uint32_t)0x5b9cca4fU, (uint32_t)0x682e6ff3U,
    (uint32_t)0x748f82eeU, (uint32_t)0x78a5636fU, (uint32_t)0x84c87814U, (uint32_t)0x8cc70208U,
    (uint32_t)0x90befffaU, (uint32_t)0xa4506cebU, (uint32_t)0xbef9a3f7U, (uint32_t)0xc67178f2U
  };

static uint64_t
k384_512[80U] =
  {
    (uint64_t)0x428a2f98d728ae22U, (uint64_t)0x7137449123ef65cdU, (uint64_t)0xb5c0fbcfec4d3b2fU,
    (uint64_t)0xe9b5dba58189dbbcU, (uint64_t)0x3956c25bf348b538U, (uint64_t)0x59f111f1b605d019U,
    (uint64_t)0x923f82a4af194f9bU, (uint64_t)0xab1c5ed5da6d8118U, (uint64_t)0xd807aa98a3030242U,
    (uint64_t)0x12835b0145706fbeU, (uint64_t)0x243185be4ee4b28cU, (uint64_t)0x550c7dc3d5ffb4e2U,
    (uint64_t)0x72be5d74f27b896fU, (uint64_t)0x80deb1fe3b1696b1U, (uint64_t)0x9bdc06a725c71235U,
    (uint64_t)0xc19bf174cf692694U, (uint64_t)0xe49b69c19ef14ad2U, (uint64_t)0xefbe4786384f25e3U,
    (uint64_t)0x0fc19dc68b8cd5b5U, (uint64_t)0x240ca1cc77ac9c65U, (uint64_t)0x2de92c6f592b0275U,
    (uint64_t)0x4a7484aa6ea6e483U, (uint64_t)0x5cb0a9dcbd41fbd4U, (uint64_t)0x76f988da831153b5U,
    (uint64_t)0x983e5152ee66dfabU, (uint64_t)0xa831c66d2db43210U, (uint64_t)0xb00327c898fb213fU,
    (uint64_t)0xbf597fc7beef0ee4U, (uint64_t)0xc6e00bf33da88fc2U, (uint64_t)0xd5a79147930aa725U,
    (uint64_t)0x06ca6351e003826fU, (uint64_t)0x142929670a0e6e70U, (uint64_t)0x27b70a8546d22ffcU,
    (uint64_t)0x2e1b21385c26c926U, (uint64_t)0x4d2c6dfc5ac42aedU, (uint64_t)0x53380d139d95b3dfU,
    (uint64_t)0x650a73548baf63deU, (uint64_t)0x766a0abb3c77b2a8U, (uint64_t)0x81c2c92e47edaee6U,
    (uint64_t)0x92722c851482353bU, (uint64_t)0xa2bfe8a14cf10364U, (uint64_t)0xa81a664bbc423001U,
    (uint64_t)0xc24b8b70d0f89791U, (uint64_t)0xc76c51a30654be30U, (uint64_t)0xd192e819d6ef5218U,
    (uint64_t)0xd69906245565a910U, (uint64_t)0xf40e35855771202aU, (uint64_t)0x106aa07032bbd1b8U,
    (uint64_t)0x19a4c116b8d2d0c8U, (uint64_t)0x1e376c085141ab53U, (uint64_t)0x2748774cdf8eeb99U,
    (uint64_t)0x34b0bcb5e19b48a8U, (uint64_t)0x391c0cb3c5c95a63U, (uint64_t)0x4ed8aa4ae3418acbU,
    (uint64_t)0x5b9cca4f7763e373U, (uint64_t)0x682e6ff3d6b2b8a3U, (uint64_t)0x748f82ee5defb2fcU,
    (uint64_t)0x78a5636f43172f60U, (uint64_t)0x84c87814a1f0ab72U, (uint64_t)0x8cc702081a6439ecU,
    (uint64_t)0x90befffa23631e28U, (uint64_t)0xa4506cebde82bde9U, (uint64_t)0xbef9a3f7b2c67915U,
    (uint64_t)0xc67178f2e372532bU, (uint64_t)0xca273eceea26619cU, (uint64_t)0xd186b8c721c0c207U,
    (uint64_t)0xeada7dd6cde0eb1eU, (uint64_t)0xf57d4f7fee6ed178U, (uint64_t)0x06f067aa72176fbaU,
    (uint64_t)0x0a637dc5a2c898a6U, (uint64_t)0x113f9804bef90daeU, (uint64_t)0x1b710b35131c471bU,
    (uint64_t)0x28db77f523047d84U, (uint64_t)0x32caab7b40c72493U, (uint64_t)0x3c9ebe0a15c9bebcU,
    (uint64_t)0x431d67c49c100d4cU, (uint64_t)0x4cc5d4becb3e42b6U, (uint64_t)0x597f299cfc657e2aU,
    (uint64_t)0x5fcb6fab3ad6faecU, (uint64_t)0x6c44198c4a475817U
  };

static void update_224(uint32_t *hash, uint8_t *block)
{
  uint32_t hash1[8U] = { 0U };
  uint32_t computed_ws[64U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    if (i < (uint32_t)16U)
    {
      uint8_t *b = block + i * (uint32_t)4U;
      uint32_t u = load32_be(b);
      computed_ws[i] = u;
    }
    else
    {
      uint32_t t16 = computed_ws[i - (uint32_t)16U];
      uint32_t t15 = computed_ws[i - (uint32_t)15U];
      uint32_t t7 = computed_ws[i - (uint32_t)7U];
      uint32_t t2 = computed_ws[i - (uint32_t)2U];
      uint32_t
      s1 =
        (t2 >> (uint32_t)17U | t2 << (uint32_t)15U)
        ^ ((t2 >> (uint32_t)19U | t2 << (uint32_t)13U) ^ t2 >> (uint32_t)10U);
      uint32_t
      s0 =
        (t15 >> (uint32_t)7U | t15 << (uint32_t)25U)
        ^ ((t15 >> (uint32_t)18U | t15 << (uint32_t)14U) ^ t15 >> (uint32_t)3U);
      uint32_t w = s1 + t7 + s0 + t16;
      computed_ws[i] = w;
    }
  }
  memcpy(hash1, hash, (uint32_t)8U * sizeof (uint32_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint32_t a0 = hash1[0U];
    uint32_t b0 = hash1[1U];
    uint32_t c0 = hash1[2U];
    uint32_t d0 = hash1[3U];
    uint32_t e0 = hash1[4U];
    uint32_t f0 = hash1[5U];
    uint32_t g0 = hash1[6U];
    uint32_t h02 = hash1[7U];
    uint32_t w = computed_ws[i];
    uint32_t
    t1 =
      h02
      +
        ((e0 >> (uint32_t)6U | e0 << (uint32_t)26U)
        ^ ((e0 >> (uint32_t)11U | e0 << (uint32_t)21U) ^ (e0 >> (uint32_t)25U | e0 << (uint32_t)7U)))
      + ((e0 & f0) ^ (~e0 & g0))
      + k224_256[i]
      + w;
    uint32_t
    t2 =
      ((a0 >> (uint32_t)2U | a0 << (uint32_t)30U)
      ^ ((a0 >> (uint32_t)13U | a0 << (uint32_t)19U) ^ (a0 >> (uint32_t)22U | a0 << (uint32_t)10U)))
      + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
    hash1[0U] = t1 + t2;
    hash1[1U] = a0;
    hash1[2U] = b0;
    hash1[3U] = c0;
    hash1[4U] = d0 + t1;
    hash1[5U] = e0;
    hash1[6U] = f0;
    hash1[7U] = g0;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t xi = hash[i];
    uint32_t yi = hash1[i];
    hash[i] = xi + yi;
  }
}

static void update_256(uint32_t *hash, uint8_t *block)
{
  uint32_t hash1[8U] = { 0U };
  uint32_t computed_ws[64U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    if (i < (uint32_t)16U)
    {
      uint8_t *b = block + i * (uint32_t)4U;
      uint32_t u = load32_be(b);
      computed_ws[i] = u;
    }
    else
    {
      uint32_t t16 = computed_ws[i - (uint32_t)16U];
      uint32_t t15 = computed_ws[i - (uint32_t)15U];
      uint32_t t7 = computed_ws[i - (uint32_t)7U];
      uint32_t t2 = computed_ws[i - (uint32_t)2U];
      uint32_t
      s1 =
        (t2 >> (uint32_t)17U | t2 << (uint32_t)15U)
        ^ ((t2 >> (uint32_t)19U | t2 << (uint32_t)13U) ^ t2 >> (uint32_t)10U);
      uint32_t
      s0 =
        (t15 >> (uint32_t)7U | t15 << (uint32_t)25U)
        ^ ((t15 >> (uint32_t)18U | t15 << (uint32_t)14U) ^ t15 >> (uint32_t)3U);
      uint32_t w = s1 + t7 + s0 + t16;
      computed_ws[i] = w;
    }
  }
  memcpy(hash1, hash, (uint32_t)8U * sizeof (uint32_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint32_t a0 = hash1[0U];
    uint32_t b0 = hash1[1U];
    uint32_t c0 = hash1[2U];
    uint32_t d0 = hash1[3U];
    uint32_t e0 = hash1[4U];
    uint32_t f0 = hash1[5U];
    uint32_t g0 = hash1[6U];
    uint32_t h02 = hash1[7U];
    uint32_t w = computed_ws[i];
    uint32_t
    t1 =
      h02
      +
        ((e0 >> (uint32_t)6U | e0 << (uint32_t)26U)
        ^ ((e0 >> (uint32_t)11U | e0 << (uint32_t)21U) ^ (e0 >> (uint32_t)25U | e0 << (uint32_t)7U)))
      + ((e0 & f0) ^ (~e0 & g0))
      + k224_256[i]
      + w;
    uint32_t
    t2 =
      ((a0 >> (uint32_t)2U | a0 << (uint32_t)30U)
      ^ ((a0 >> (uint32_t)13U | a0 << (uint32_t)19U) ^ (a0 >> (uint32_t)22U | a0 << (uint32_t)10U)))
      + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
    hash1[0U] = t1 + t2;
    hash1[1U] = a0;
    hash1[2U] = b0;
    hash1[3U] = c0;
    hash1[4U] = d0 + t1;
    hash1[5U] = e0;
    hash1[6U] = f0;
    hash1[7U] = g0;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t xi = hash[i];
    uint32_t yi = hash1[i];
    hash[i] = xi + yi;
  }
}

static void update_384(uint64_t *hash, uint8_t *block)
{
  uint64_t hash1[8U] = { 0U };
  uint64_t computed_ws[80U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)80U; i++)
  {
    if (i < (uint32_t)16U)
    {
      uint8_t *b = block + i * (uint32_t)8U;
      uint64_t u = load64_be(b);
      computed_ws[i] = u;
    }
    else
    {
      uint64_t t16 = computed_ws[i - (uint32_t)16U];
      uint64_t t15 = computed_ws[i - (uint32_t)15U];
      uint64_t t7 = computed_ws[i - (uint32_t)7U];
      uint64_t t2 = computed_ws[i - (uint32_t)2U];
      uint64_t
      s1 =
        (t2 >> (uint32_t)19U | t2 << (uint32_t)45U)
        ^ ((t2 >> (uint32_t)61U | t2 << (uint32_t)3U) ^ t2 >> (uint32_t)6U);
      uint64_t
      s0 =
        (t15 >> (uint32_t)1U | t15 << (uint32_t)63U)
        ^ ((t15 >> (uint32_t)8U | t15 << (uint32_t)56U) ^ t15 >> (uint32_t)7U);
      uint64_t w = s1 + t7 + s0 + t16;
      computed_ws[i] = w;
    }
  }
  memcpy(hash1, hash, (uint32_t)8U * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)80U; i++)
  {
    uint64_t a0 = hash1[0U];
    uint64_t b0 = hash1[1U];
    uint64_t c0 = hash1[2U];
    uint64_t d0 = hash1[3U];
    uint64_t e0 = hash1[4U];
    uint64_t f0 = hash1[5U];
    uint64_t g0 = hash1[6U];
    uint64_t h02 = hash1[7U];
    uint64_t w = computed_ws[i];
    uint64_t
    t1 =
      h02
      +
        ((e0 >> (uint32_t)14U | e0 << (uint32_t)50U)
        ^
          ((e0 >> (uint32_t)18U | e0 << (uint32_t)46U)
          ^ (e0 >> (uint32_t)41U | e0 << (uint32_t)23U)))
      + ((e0 & f0) ^ (~e0 & g0))
      + k384_512[i]
      + w;
    uint64_t
    t2 =
      ((a0 >> (uint32_t)28U | a0 << (uint32_t)36U)
      ^ ((a0 >> (uint32_t)34U | a0 << (uint32_t)30U) ^ (a0 >> (uint32_t)39U | a0 << (uint32_t)25U)))
      + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
    hash1[0U] = t1 + t2;
    hash1[1U] = a0;
    hash1[2U] = b0;
    hash1[3U] = c0;
    hash1[4U] = d0 + t1;
    hash1[5U] = e0;
    hash1[6U] = f0;
    hash1[7U] = g0;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t xi = hash[i];
    uint64_t yi = hash1[i];
    hash[i] = xi + yi;
  }
}

static void update_512(uint64_t *hash, uint8_t *block)
{
  uint64_t hash1[8U] = { 0U };
  uint64_t computed_ws[80U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)80U; i++)
  {
    if (i < (uint32_t)16U)
    {
      uint8_t *b = block + i * (uint32_t)8U;
      uint64_t u = load64_be(b);
      computed_ws[i] = u;
    }
    else
    {
      uint64_t t16 = computed_ws[i - (uint32_t)16U];
      uint64_t t15 = computed_ws[i - (uint32_t)15U];
      uint64_t t7 = computed_ws[i - (uint32_t)7U];
      uint64_t t2 = computed_ws[i - (uint32_t)2U];
      uint64_t
      s1 =
        (t2 >> (uint32_t)19U | t2 << (uint32_t)45U)
        ^ ((t2 >> (uint32_t)61U | t2 << (uint32_t)3U) ^ t2 >> (uint32_t)6U);
      uint64_t
      s0 =
        (t15 >> (uint32_t)1U | t15 << (uint32_t)63U)
        ^ ((t15 >> (uint32_t)8U | t15 << (uint32_t)56U) ^ t15 >> (uint32_t)7U);
      uint64_t w = s1 + t7 + s0 + t16;
      computed_ws[i] = w;
    }
  }
  memcpy(hash1, hash, (uint32_t)8U * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)80U; i++)
  {
    uint64_t a0 = hash1[0U];
    uint64_t b0 = hash1[1U];
    uint64_t c0 = hash1[2U];
    uint64_t d0 = hash1[3U];
    uint64_t e0 = hash1[4U];
    uint64_t f0 = hash1[5U];
    uint64_t g0 = hash1[6U];
    uint64_t h02 = hash1[7U];
    uint64_t w = computed_ws[i];
    uint64_t
    t1 =
      h02
      +
        ((e0 >> (uint32_t)14U | e0 << (uint32_t)50U)
        ^
          ((e0 >> (uint32_t)18U | e0 << (uint32_t)46U)
          ^ (e0 >> (uint32_t)41U | e0 << (uint32_t)23U)))
      + ((e0 & f0) ^ (~e0 & g0))
      + k384_512[i]
      + w;
    uint64_t
    t2 =
      ((a0 >> (uint32_t)28U | a0 << (uint32_t)36U)
      ^ ((a0 >> (uint32_t)34U | a0 << (uint32_t)30U) ^ (a0 >> (uint32_t)39U | a0 << (uint32_t)25U)))
      + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
    hash1[0U] = t1 + t2;
    hash1[1U] = a0;
    hash1[2U] = b0;
    hash1[3U] = c0;
    hash1[4U] = d0 + t1;
    hash1[5U] = e0;
    hash1[6U] = f0;
    hash1[7U] = g0;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t xi = hash[i];
    uint64_t yi = hash1[i];
    hash[i] = xi + yi;
  }
}

static void pad_224(uint64_t len, uint8_t *dst)
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

static void pad_256(uint64_t len, uint8_t *dst)
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

static void pad_384(FStar_UInt128_uint128 len, uint8_t *dst)
{
  uint8_t *dst1 = dst;
  dst1[0U] = (uint8_t)0x80U;
  uint8_t *dst2 = dst + (uint32_t)1U;
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    <
      ((uint32_t)256U
      -
        ((uint32_t)17U
        + (uint32_t)(FStar_UInt128_uint128_to_uint64(len) % (uint64_t)(uint32_t)128U)))
      % (uint32_t)128U;
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
        ((uint32_t)256U
        -
          ((uint32_t)17U
          + (uint32_t)(FStar_UInt128_uint128_to_uint64(len) % (uint64_t)(uint32_t)128U)))
        % (uint32_t)128U;
  FStar_UInt128_uint128 len_ = FStar_UInt128_shift_left(len, (uint32_t)3U);
  store128_be(dst3, len_);
}

static void pad_512(FStar_UInt128_uint128 len, uint8_t *dst)
{
  uint8_t *dst1 = dst;
  dst1[0U] = (uint8_t)0x80U;
  uint8_t *dst2 = dst + (uint32_t)1U;
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    <
      ((uint32_t)256U
      -
        ((uint32_t)17U
        + (uint32_t)(FStar_UInt128_uint128_to_uint64(len) % (uint64_t)(uint32_t)128U)))
      % (uint32_t)128U;
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
        ((uint32_t)256U
        -
          ((uint32_t)17U
          + (uint32_t)(FStar_UInt128_uint128_to_uint64(len) % (uint64_t)(uint32_t)128U)))
        % (uint32_t)128U;
  FStar_UInt128_uint128 len_ = FStar_UInt128_shift_left(len, (uint32_t)3U);
  store128_be(dst3, len_);
}

static void finish_224(uint32_t *s, uint8_t *dst)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)7U; i++)
  {
    store32_be(dst + i * (uint32_t)4U, s[i]);
  }
}

static void finish_256(uint32_t *s, uint8_t *dst)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    store32_be(dst + i * (uint32_t)4U, s[i]);
  }
}

static void finish_384(uint64_t *s, uint8_t *dst)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)6U; i++)
  {
    store64_be(dst + i * (uint32_t)8U, s[i]);
  }
}

static void finish_512(uint64_t *s, uint8_t *dst)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    store64_be(dst + i * (uint32_t)8U, s[i]);
  }
}

static void update_multi_224(uint32_t *s, uint8_t *blocks, uint32_t n_blocks)
{
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i++)
  {
    uint32_t sz = (uint32_t)64U;
    uint8_t *block = blocks + sz * i;
    update_224(s, block);
  }
}

static void update_multi_256(uint32_t *s, uint8_t *blocks, uint32_t n_blocks)
{
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i++)
  {
    uint32_t sz = (uint32_t)64U;
    uint8_t *block = blocks + sz * i;
    update_256(s, block);
  }
}

static void update_multi_384(uint64_t *s, uint8_t *blocks, uint32_t n_blocks)
{
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i++)
  {
    uint32_t sz = (uint32_t)128U;
    uint8_t *block = blocks + sz * i;
    update_384(s, block);
  }
}

static void update_multi_512(uint64_t *s, uint8_t *blocks, uint32_t n_blocks)
{
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i++)
  {
    uint32_t sz = (uint32_t)128U;
    uint8_t *block = blocks + sz * i;
    update_512(s, block);
  }
}

static void update_last_224(uint32_t *s, uint64_t prev_len, uint8_t *input, uint32_t input_len)
{
  uint32_t blocks_n = input_len / (uint32_t)64U;
  uint32_t blocks_len = blocks_n * (uint32_t)64U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  update_multi_224(s, blocks, blocks_n);
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
  pad_224(total_input_len, tmp_pad);
  update_multi_224(s, tmp, tmp_len / (uint32_t)64U);
}

static void update_last_256(uint32_t *s, uint64_t prev_len, uint8_t *input, uint32_t input_len)
{
  uint32_t blocks_n = input_len / (uint32_t)64U;
  uint32_t blocks_len = blocks_n * (uint32_t)64U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  update_multi_256(s, blocks, blocks_n);
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
  pad_256(total_input_len, tmp_pad);
  update_multi_256(s, tmp, tmp_len / (uint32_t)64U);
}

static void
update_last_384(
  uint64_t *s,
  FStar_UInt128_uint128 prev_len,
  uint8_t *input,
  uint32_t input_len
)
{
  uint32_t blocks_n = input_len / (uint32_t)128U;
  uint32_t blocks_len = blocks_n * (uint32_t)128U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  update_multi_384(s, blocks, blocks_n);
  FStar_UInt128_uint128
  total_input_len =
    FStar_UInt128_add(prev_len,
      FStar_UInt128_uint64_to_uint128((uint64_t)input_len));
  uint32_t
  pad_len =
    (uint32_t)1U
    +
      ((uint32_t)256U
      -
        ((uint32_t)17U
        + (uint32_t)(FStar_UInt128_uint128_to_uint64(total_input_len) % (uint64_t)(uint32_t)128U)))
      % (uint32_t)128U
    + (uint32_t)16U;
  uint32_t tmp_len = rest_len + pad_len;
  uint8_t tmp_twoblocks[256U] = { 0U };
  uint8_t *tmp = tmp_twoblocks;
  uint8_t *tmp_rest = tmp;
  uint8_t *tmp_pad = tmp + rest_len;
  memcpy(tmp_rest, rest, rest_len * sizeof (uint8_t));
  pad_384(total_input_len, tmp_pad);
  update_multi_384(s, tmp, tmp_len / (uint32_t)128U);
}

static void
update_last_512(
  uint64_t *s,
  FStar_UInt128_uint128 prev_len,
  uint8_t *input,
  uint32_t input_len
)
{
  uint32_t blocks_n = input_len / (uint32_t)128U;
  uint32_t blocks_len = blocks_n * (uint32_t)128U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  update_multi_512(s, blocks, blocks_n);
  FStar_UInt128_uint128
  total_input_len =
    FStar_UInt128_add(prev_len,
      FStar_UInt128_uint64_to_uint128((uint64_t)input_len));
  uint32_t
  pad_len =
    (uint32_t)1U
    +
      ((uint32_t)256U
      -
        ((uint32_t)17U
        + (uint32_t)(FStar_UInt128_uint128_to_uint64(total_input_len) % (uint64_t)(uint32_t)128U)))
      % (uint32_t)128U
    + (uint32_t)16U;
  uint32_t tmp_len = rest_len + pad_len;
  uint8_t tmp_twoblocks[256U] = { 0U };
  uint8_t *tmp = tmp_twoblocks;
  uint8_t *tmp_rest = tmp;
  uint8_t *tmp_pad = tmp + rest_len;
  memcpy(tmp_rest, rest, rest_len * sizeof (uint8_t));
  pad_512(total_input_len, tmp_pad);
  update_multi_512(s, tmp, tmp_len / (uint32_t)128U);
}

typedef uint32_t *___uint32_t____;

static void hash_224(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint32_t
  scrut[8U] =
    {
      (uint32_t)0xc1059ed8U, (uint32_t)0x367cd507U, (uint32_t)0x3070dd17U, (uint32_t)0xf70e5939U,
      (uint32_t)0xffc00b31U, (uint32_t)0x68581511U, (uint32_t)0x64f98fa7U, (uint32_t)0xbefa4fa4U
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
  update_multi_224(s, blocks, blocks_n);
  update_last_224(s, (uint64_t)blocks_len, rest, rest_len);
  finish_224(s, dst);
}

static void hash_256(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint32_t
  scrut[8U] =
    {
      (uint32_t)0x6a09e667U, (uint32_t)0xbb67ae85U, (uint32_t)0x3c6ef372U, (uint32_t)0xa54ff53aU,
      (uint32_t)0x510e527fU, (uint32_t)0x9b05688cU, (uint32_t)0x1f83d9abU, (uint32_t)0x5be0cd19U
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
  update_multi_256(s, blocks, blocks_n);
  update_last_256(s, (uint64_t)blocks_len, rest, rest_len);
  finish_256(s, dst);
}

typedef uint64_t *___uint64_t____;

static void hash_384(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint64_t
  scrut[8U] =
    {
      (uint64_t)0xcbbb9d5dc1059ed8U, (uint64_t)0x629a292a367cd507U, (uint64_t)0x9159015a3070dd17U,
      (uint64_t)0x152fecd8f70e5939U, (uint64_t)0x67332667ffc00b31U, (uint64_t)0x8eb44a8768581511U,
      (uint64_t)0xdb0c2e0d64f98fa7U, (uint64_t)0x47b5481dbefa4fa4U
    };
  uint64_t *s = scrut;
  uint32_t blocks_n0 = input_len / (uint32_t)128U;
  uint32_t blocks_n1;
  if (input_len % (uint32_t)128U == (uint32_t)0U && blocks_n0 > (uint32_t)0U)
  {
    blocks_n1 = blocks_n0 - (uint32_t)1U;
  }
  else
  {
    blocks_n1 = blocks_n0;
  }
  uint32_t blocks_len0 = blocks_n1 * (uint32_t)128U;
  uint8_t *blocks0 = input;
  uint32_t rest_len0 = input_len - blocks_len0;
  uint8_t *rest0 = input + blocks_len0;
  uint32_t blocks_n = blocks_n1;
  uint32_t blocks_len = blocks_len0;
  uint8_t *blocks = blocks0;
  uint32_t rest_len = rest_len0;
  uint8_t *rest = rest0;
  update_multi_384(s, blocks, blocks_n);
  update_last_384(s, FStar_UInt128_uint64_to_uint128((uint64_t)blocks_len), rest, rest_len);
  finish_384(s, dst);
}

static void hash_512(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint64_t
  scrut[8U] =
    {
      (uint64_t)0x6a09e667f3bcc908U, (uint64_t)0xbb67ae8584caa73bU, (uint64_t)0x3c6ef372fe94f82bU,
      (uint64_t)0xa54ff53a5f1d36f1U, (uint64_t)0x510e527fade682d1U, (uint64_t)0x9b05688c2b3e6c1fU,
      (uint64_t)0x1f83d9abfb41bd6bU, (uint64_t)0x5be0cd19137e2179U
    };
  uint64_t *s = scrut;
  uint32_t blocks_n0 = input_len / (uint32_t)128U;
  uint32_t blocks_n1;
  if (input_len % (uint32_t)128U == (uint32_t)0U && blocks_n0 > (uint32_t)0U)
  {
    blocks_n1 = blocks_n0 - (uint32_t)1U;
  }
  else
  {
    blocks_n1 = blocks_n0;
  }
  uint32_t blocks_len0 = blocks_n1 * (uint32_t)128U;
  uint8_t *blocks0 = input;
  uint32_t rest_len0 = input_len - blocks_len0;
  uint8_t *rest0 = input + blocks_len0;
  uint32_t blocks_n = blocks_n1;
  uint32_t blocks_len = blocks_len0;
  uint8_t *blocks = blocks0;
  uint32_t rest_len = rest_len0;
  uint8_t *rest = rest0;
  update_multi_512(s, blocks, blocks_n);
  update_last_512(s, FStar_UInt128_uint64_to_uint128((uint64_t)blocks_len), rest, rest_len);
  finish_512(s, dst);
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

exit_code main()
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

