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

typedef uint8_t hash_alg;

static uint32_t
h256[8U] =
  {
    (uint32_t)0x6a09e667U, (uint32_t)0xbb67ae85U, (uint32_t)0x3c6ef372U, (uint32_t)0xa54ff53aU,
    (uint32_t)0x510e527fU, (uint32_t)0x9b05688cU, (uint32_t)0x1f83d9abU, (uint32_t)0x5be0cd19U
  };

static uint64_t
h384[8U] =
  {
    (uint64_t)0xcbbb9d5dc1059ed8U, (uint64_t)0x629a292a367cd507U, (uint64_t)0x9159015a3070dd17U,
    (uint64_t)0x152fecd8f70e5939U, (uint64_t)0x67332667ffc00b31U, (uint64_t)0x8eb44a8768581511U,
    (uint64_t)0xdb0c2e0d64f98fa7U, (uint64_t)0x47b5481dbefa4fa4U
  };

static uint64_t
h512[8U] =
  {
    (uint64_t)0x6a09e667f3bcc908U, (uint64_t)0xbb67ae8584caa73bU, (uint64_t)0x3c6ef372fe94f82bU,
    (uint64_t)0xa54ff53a5f1d36f1U, (uint64_t)0x510e527fade682d1U, (uint64_t)0x9b05688c2b3e6c1fU,
    (uint64_t)0x1f83d9abfb41bd6bU, (uint64_t)0x5be0cd19137e2179U
  };

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

static void init_256(uint32_t *s)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    s[i] = h256[i];
  }
}

static void init_384(uint64_t *s)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    s[i] = h384[i];
  }
}

static void init_512(uint64_t *s)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    s[i] = h512[i];
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

static uint32_t
_h0[5U] =
  {
    (uint32_t)0x67452301U, (uint32_t)0xefcdab89U, (uint32_t)0x98badcfeU, (uint32_t)0x10325476U,
    (uint32_t)0xc3d2e1f0U
  };

static void legacy_init(uint32_t *s)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)5U; i++)
  {
    s[i] = _h0[i];
  }
}

static void legacy_update(uint32_t *h, uint8_t *l)
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

static void legacy_finish(uint32_t *s, uint8_t *dst)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)5U; i++)
  {
    store32_be(dst + i * (uint32_t)4U, s[i]);
  }
}

static void legacy_update_multi(uint32_t *s, uint8_t *blocks, uint32_t n_blocks)
{
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i++)
  {
    uint32_t sz = (uint32_t)64U;
    uint8_t *block = blocks + sz * i;
    legacy_update(s, block);
  }
}

static void
legacy_update_last(uint32_t *s, uint64_t prev_len, uint8_t *input, uint32_t input_len)
{
  uint32_t blocks_n = input_len / (uint32_t)64U;
  uint32_t blocks_len = blocks_n * (uint32_t)64U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  legacy_update_multi(s, blocks, blocks_n);
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
  legacy_update_multi(s, tmp, tmp_len / (uint32_t)64U);
}

static void legacy_hash(uint8_t *input, uint32_t input_len, uint8_t *dst)
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
  legacy_update_multi(s, blocks, blocks_n);
  legacy_update_last(s, (uint64_t)blocks_len, rest, rest_len);
  legacy_finish(s, dst);
}

extern void C_String_print(C_String_t uu___);

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
legacy_compute_sha1(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
)
{
  uint32_t l = (uint32_t)64U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t key_block[l];
  memset(key_block, 0U, l * sizeof (uint8_t));
  uint32_t i0;
  if (key_len <= (uint32_t)64U)
  {
    i0 = key_len;
  }
  else
  {
    i0 = (uint32_t)20U;
  }
  uint8_t *nkey = key_block;
  if (key_len <= (uint32_t)64U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));
  }
  else
  {
    legacy_hash(key, key_len, nkey);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t ipad[l];
  memset(ipad, (uint8_t)0x36U, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = xi ^ yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t opad[l];
  memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = xi ^ yi;
  }
  uint32_t
  scrut0[5U] =
    {
      (uint32_t)0x67452301U, (uint32_t)0xefcdab89U, (uint32_t)0x98badcfeU, (uint32_t)0x10325476U,
      (uint32_t)0xc3d2e1f0U
    };
  uint32_t *s = scrut0;
  uint8_t *dst1 = ipad;
  legacy_init(s);
  if (data_len == (uint32_t)0U)
  {
    legacy_update_last(s, (uint64_t)0U, ipad, (uint32_t)64U);
  }
  else
  {
    legacy_update_multi(s, ipad, (uint32_t)1U);
    uint32_t block_len = (uint32_t)64U;
    uint32_t n_blocks0 = data_len / block_len;
    uint32_t rem = data_len % block_len;
    __uint32_t_uint32_t scrut;
    if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
    {
      uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = data_len - n_blocks_ * block_len });
    }
    else
    {
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
    }
    uint32_t n_blocks = scrut.fst;
    uint32_t rem_len = scrut.snd;
    uint32_t full_blocks_len = n_blocks * block_len;
    uint8_t *full_blocks = data;
    legacy_update_multi(s, full_blocks, n_blocks);
    uint8_t *rem0 = data + full_blocks_len;
    legacy_update_last(s, (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len, rem0, rem_len);
  }
  legacy_finish(s, dst1);
  uint8_t *hash1 = ipad;
  legacy_init(s);
  legacy_update_multi(s, opad, (uint32_t)1U);
  uint32_t block_len = (uint32_t)64U;
  uint32_t n_blocks0 = (uint32_t)20U / block_len;
  uint32_t rem = (uint32_t)20U % block_len;
  __uint32_t_uint32_t scrut;
  if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
  {
    uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
    scrut =
      ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = (uint32_t)20U - n_blocks_ * block_len });
  }
  else
  {
    scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
  }
  uint32_t n_blocks = scrut.fst;
  uint32_t rem_len = scrut.snd;
  uint32_t full_blocks_len = n_blocks * block_len;
  uint8_t *full_blocks = hash1;
  legacy_update_multi(s, full_blocks, n_blocks);
  uint8_t *rem0 = hash1 + full_blocks_len;
  legacy_update_last(s, (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len, rem0, rem_len);
  legacy_finish(s, dst);
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
  uint32_t l = (uint32_t)64U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t key_block[l];
  memset(key_block, 0U, l * sizeof (uint8_t));
  uint32_t i0;
  if (key_len <= (uint32_t)64U)
  {
    i0 = key_len;
  }
  else
  {
    i0 = (uint32_t)32U;
  }
  uint8_t *nkey = key_block;
  if (key_len <= (uint32_t)64U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));
  }
  else
  {
    hash_256(key, key_len, nkey);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t ipad[l];
  memset(ipad, (uint8_t)0x36U, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = xi ^ yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t opad[l];
  memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = xi ^ yi;
  }
  uint32_t
  scrut0[8U] =
    {
      (uint32_t)0x6a09e667U, (uint32_t)0xbb67ae85U, (uint32_t)0x3c6ef372U, (uint32_t)0xa54ff53aU,
      (uint32_t)0x510e527fU, (uint32_t)0x9b05688cU, (uint32_t)0x1f83d9abU, (uint32_t)0x5be0cd19U
    };
  uint32_t *s = scrut0;
  uint8_t *dst1 = ipad;
  init_256(s);
  if (data_len == (uint32_t)0U)
  {
    update_last_256(s, (uint64_t)0U, ipad, (uint32_t)64U);
  }
  else
  {
    update_multi_256(s, ipad, (uint32_t)1U);
    uint32_t block_len = (uint32_t)64U;
    uint32_t n_blocks0 = data_len / block_len;
    uint32_t rem = data_len % block_len;
    __uint32_t_uint32_t scrut;
    if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
    {
      uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = data_len - n_blocks_ * block_len });
    }
    else
    {
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
    }
    uint32_t n_blocks = scrut.fst;
    uint32_t rem_len = scrut.snd;
    uint32_t full_blocks_len = n_blocks * block_len;
    uint8_t *full_blocks = data;
    update_multi_256(s, full_blocks, n_blocks);
    uint8_t *rem0 = data + full_blocks_len;
    update_last_256(s, (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len, rem0, rem_len);
  }
  finish_256(s, dst1);
  uint8_t *hash1 = ipad;
  init_256(s);
  update_multi_256(s, opad, (uint32_t)1U);
  uint32_t block_len = (uint32_t)64U;
  uint32_t n_blocks0 = (uint32_t)32U / block_len;
  uint32_t rem = (uint32_t)32U % block_len;
  __uint32_t_uint32_t scrut;
  if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
  {
    uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
    scrut =
      ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = (uint32_t)32U - n_blocks_ * block_len });
  }
  else
  {
    scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
  }
  uint32_t n_blocks = scrut.fst;
  uint32_t rem_len = scrut.snd;
  uint32_t full_blocks_len = n_blocks * block_len;
  uint8_t *full_blocks = hash1;
  update_multi_256(s, full_blocks, n_blocks);
  uint8_t *rem0 = hash1 + full_blocks_len;
  update_last_256(s, (uint64_t)(uint32_t)64U + (uint64_t)full_blocks_len, rem0, rem_len);
  finish_256(s, dst);
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
  uint32_t l = (uint32_t)128U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t key_block[l];
  memset(key_block, 0U, l * sizeof (uint8_t));
  uint32_t i0;
  if (key_len <= (uint32_t)128U)
  {
    i0 = key_len;
  }
  else
  {
    i0 = (uint32_t)48U;
  }
  uint8_t *nkey = key_block;
  if (key_len <= (uint32_t)128U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));
  }
  else
  {
    hash_384(key, key_len, nkey);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t ipad[l];
  memset(ipad, (uint8_t)0x36U, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = xi ^ yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t opad[l];
  memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = xi ^ yi;
  }
  uint64_t
  scrut0[8U] =
    {
      (uint64_t)0xcbbb9d5dc1059ed8U, (uint64_t)0x629a292a367cd507U, (uint64_t)0x9159015a3070dd17U,
      (uint64_t)0x152fecd8f70e5939U, (uint64_t)0x67332667ffc00b31U, (uint64_t)0x8eb44a8768581511U,
      (uint64_t)0xdb0c2e0d64f98fa7U, (uint64_t)0x47b5481dbefa4fa4U
    };
  uint64_t *s = scrut0;
  uint8_t *dst1 = ipad;
  init_384(s);
  if (data_len == (uint32_t)0U)
  {
    update_last_384(s, FStar_UInt128_uint64_to_uint128((uint64_t)0U), ipad, (uint32_t)128U);
  }
  else
  {
    update_multi_384(s, ipad, (uint32_t)1U);
    uint32_t block_len = (uint32_t)128U;
    uint32_t n_blocks0 = data_len / block_len;
    uint32_t rem = data_len % block_len;
    __uint32_t_uint32_t scrut;
    if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
    {
      uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = data_len - n_blocks_ * block_len });
    }
    else
    {
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
    }
    uint32_t n_blocks = scrut.fst;
    uint32_t rem_len = scrut.snd;
    uint32_t full_blocks_len = n_blocks * block_len;
    uint8_t *full_blocks = data;
    update_multi_384(s, full_blocks, n_blocks);
    uint8_t *rem0 = data + full_blocks_len;
    update_last_384(s,
      FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
        FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
      rem0,
      rem_len);
  }
  finish_384(s, dst1);
  uint8_t *hash1 = ipad;
  init_384(s);
  update_multi_384(s, opad, (uint32_t)1U);
  uint32_t block_len = (uint32_t)128U;
  uint32_t n_blocks0 = (uint32_t)48U / block_len;
  uint32_t rem = (uint32_t)48U % block_len;
  __uint32_t_uint32_t scrut;
  if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
  {
    uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
    scrut =
      ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = (uint32_t)48U - n_blocks_ * block_len });
  }
  else
  {
    scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
  }
  uint32_t n_blocks = scrut.fst;
  uint32_t rem_len = scrut.snd;
  uint32_t full_blocks_len = n_blocks * block_len;
  uint8_t *full_blocks = hash1;
  update_multi_384(s, full_blocks, n_blocks);
  uint8_t *rem0 = hash1 + full_blocks_len;
  update_last_384(s,
    FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
      FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
    rem0,
    rem_len);
  finish_384(s, dst);
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
  uint32_t l = (uint32_t)128U;
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t key_block[l];
  memset(key_block, 0U, l * sizeof (uint8_t));
  uint32_t i0;
  if (key_len <= (uint32_t)128U)
  {
    i0 = key_len;
  }
  else
  {
    i0 = (uint32_t)64U;
  }
  uint8_t *nkey = key_block;
  if (key_len <= (uint32_t)128U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));
  }
  else
  {
    hash_512(key, key_len, nkey);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t ipad[l];
  memset(ipad, (uint8_t)0x36U, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = ipad[i];
    uint8_t yi = key_block[i];
    ipad[i] = xi ^ yi;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), l);
  uint8_t opad[l];
  memset(opad, (uint8_t)0x5cU, l * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < l; i++)
  {
    uint8_t xi = opad[i];
    uint8_t yi = key_block[i];
    opad[i] = xi ^ yi;
  }
  uint64_t
  scrut0[8U] =
    {
      (uint64_t)0x6a09e667f3bcc908U, (uint64_t)0xbb67ae8584caa73bU, (uint64_t)0x3c6ef372fe94f82bU,
      (uint64_t)0xa54ff53a5f1d36f1U, (uint64_t)0x510e527fade682d1U, (uint64_t)0x9b05688c2b3e6c1fU,
      (uint64_t)0x1f83d9abfb41bd6bU, (uint64_t)0x5be0cd19137e2179U
    };
  uint64_t *s = scrut0;
  uint8_t *dst1 = ipad;
  init_512(s);
  if (data_len == (uint32_t)0U)
  {
    update_last_512(s, FStar_UInt128_uint64_to_uint128((uint64_t)0U), ipad, (uint32_t)128U);
  }
  else
  {
    update_multi_512(s, ipad, (uint32_t)1U);
    uint32_t block_len = (uint32_t)128U;
    uint32_t n_blocks0 = data_len / block_len;
    uint32_t rem = data_len % block_len;
    __uint32_t_uint32_t scrut;
    if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
    {
      uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = data_len - n_blocks_ * block_len });
    }
    else
    {
      scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
    }
    uint32_t n_blocks = scrut.fst;
    uint32_t rem_len = scrut.snd;
    uint32_t full_blocks_len = n_blocks * block_len;
    uint8_t *full_blocks = data;
    update_multi_512(s, full_blocks, n_blocks);
    uint8_t *rem0 = data + full_blocks_len;
    update_last_512(s,
      FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
        FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
      rem0,
      rem_len);
  }
  finish_512(s, dst1);
  uint8_t *hash1 = ipad;
  init_512(s);
  update_multi_512(s, opad, (uint32_t)1U);
  uint32_t block_len = (uint32_t)128U;
  uint32_t n_blocks0 = (uint32_t)64U / block_len;
  uint32_t rem = (uint32_t)64U % block_len;
  __uint32_t_uint32_t scrut;
  if (n_blocks0 > (uint32_t)0U && rem == (uint32_t)0U)
  {
    uint32_t n_blocks_ = n_blocks0 - (uint32_t)1U;
    scrut =
      ((__uint32_t_uint32_t){ .fst = n_blocks_, .snd = (uint32_t)64U - n_blocks_ * block_len });
  }
  else
  {
    scrut = ((__uint32_t_uint32_t){ .fst = n_blocks0, .snd = rem });
  }
  uint32_t n_blocks = scrut.fst;
  uint32_t rem_len = scrut.snd;
  uint32_t full_blocks_len = n_blocks * block_len;
  uint8_t *full_blocks = hash1;
  update_multi_512(s, full_blocks, n_blocks);
  uint8_t *rem0 = hash1 + full_blocks_len;
  update_last_512(s,
    FStar_UInt128_add(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U),
      FStar_UInt128_uint64_to_uint128((uint64_t)full_blocks_len)),
    rem0,
    rem_len);
  finish_512(s, dst);
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

static uint32_t reseed_interval = (uint32_t)1024U;

static uint32_t max_output_length = (uint32_t)65536U;

static uint32_t max_length = (uint32_t)65536U;

static uint32_t max_personalization_string_length = (uint32_t)65536U;

static uint32_t max_additional_input_length = (uint32_t)65536U;

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
        return (uint32_t)16U;
      }
    case SHA2_256:
      {
        return (uint32_t)32U;
      }
    case SHA2_384:
      {
        return (uint32_t)32U;
      }
    case SHA2_512:
      {
        return (uint32_t)32U;
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
        memset(k, 0U, (uint32_t)20U * sizeof (uint8_t));
        memset(v, (uint8_t)1U, (uint32_t)20U * sizeof (uint8_t));
        ctr[0U] = (uint32_t)1U;
        uint32_t
        input_len = (uint32_t)21U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)20U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)21U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        }
        input0[20U] = (uint8_t)0U;
        legacy_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
        legacy_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
        memcpy(k, k_, (uint32_t)20U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          uint32_t
          input_len0 = (uint32_t)21U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)20U * sizeof (uint8_t));
          if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)21U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
          }
          input[20U] = (uint8_t)1U;
          legacy_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
          legacy_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
          memcpy(k, k_0, (uint32_t)20U * sizeof (uint8_t));
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
        memset(k, 0U, (uint32_t)32U * sizeof (uint8_t));
        memset(v, (uint8_t)1U, (uint32_t)32U * sizeof (uint8_t));
        ctr[0U] = (uint32_t)1U;
        uint32_t
        input_len = (uint32_t)33U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)32U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)33U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        }
        input0[32U] = (uint8_t)0U;
        compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
        compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
        memcpy(k, k_, (uint32_t)32U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          uint32_t
          input_len0 = (uint32_t)33U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)32U * sizeof (uint8_t));
          if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)33U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
          }
          input[32U] = (uint8_t)1U;
          compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
          compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
          memcpy(k, k_0, (uint32_t)32U * sizeof (uint8_t));
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
        memset(k, 0U, (uint32_t)48U * sizeof (uint8_t));
        memset(v, (uint8_t)1U, (uint32_t)48U * sizeof (uint8_t));
        ctr[0U] = (uint32_t)1U;
        uint32_t
        input_len = (uint32_t)49U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)48U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)49U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        }
        input0[48U] = (uint8_t)0U;
        compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
        compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
        memcpy(k, k_, (uint32_t)48U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          uint32_t
          input_len0 = (uint32_t)49U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)48U * sizeof (uint8_t));
          if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)49U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
          }
          input[48U] = (uint8_t)1U;
          compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
          compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
          memcpy(k, k_0, (uint32_t)48U * sizeof (uint8_t));
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
        memset(k, 0U, (uint32_t)64U * sizeof (uint8_t));
        memset(v, (uint8_t)1U, (uint32_t)64U * sizeof (uint8_t));
        ctr[0U] = (uint32_t)1U;
        uint32_t
        input_len = (uint32_t)65U + entropy_input_len + nonce_len + personalization_string_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)64U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)65U,
            seed_material,
            (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
        }
        input0[64U] = (uint8_t)0U;
        compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
        compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
        memcpy(k, k_, (uint32_t)64U * sizeof (uint8_t));
        if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
        {
          uint32_t
          input_len0 = (uint32_t)65U + entropy_input_len + nonce_len + personalization_string_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)64U * sizeof (uint8_t));
          if (entropy_input_len + nonce_len + personalization_string_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)65U,
              seed_material,
              (entropy_input_len + nonce_len + personalization_string_len) * sizeof (uint8_t));
          }
          input[64U] = (uint8_t)1U;
          compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
          compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
          memcpy(k, k_0, (uint32_t)64U * sizeof (uint8_t));
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
        state uu____0 = st;
        uint8_t *k = uu____0.k;
        uint8_t *v = uu____0.v;
        uint32_t *ctr = uu____0.reseed_counter;
        uint32_t input_len = (uint32_t)21U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)20U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)21U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        }
        input0[20U] = (uint8_t)0U;
        legacy_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
        legacy_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
        memcpy(k, k_, (uint32_t)20U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)21U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)20U * sizeof (uint8_t));
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)21U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
          }
          input[20U] = (uint8_t)1U;
          legacy_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
          legacy_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
          memcpy(k, k_0, (uint32_t)20U * sizeof (uint8_t));
        }
        ctr[0U] = (uint32_t)1U;
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
        state uu____1 = st;
        uint8_t *k = uu____1.k;
        uint8_t *v = uu____1.v;
        uint32_t *ctr = uu____1.reseed_counter;
        uint32_t input_len = (uint32_t)33U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)32U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)33U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        }
        input0[32U] = (uint8_t)0U;
        compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
        compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
        memcpy(k, k_, (uint32_t)32U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)33U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)32U * sizeof (uint8_t));
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)33U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
          }
          input[32U] = (uint8_t)1U;
          compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
          compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
          memcpy(k, k_0, (uint32_t)32U * sizeof (uint8_t));
        }
        ctr[0U] = (uint32_t)1U;
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
        state uu____2 = st;
        uint8_t *k = uu____2.k;
        uint8_t *v = uu____2.v;
        uint32_t *ctr = uu____2.reseed_counter;
        uint32_t input_len = (uint32_t)49U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)48U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)49U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        }
        input0[48U] = (uint8_t)0U;
        compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
        compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
        memcpy(k, k_, (uint32_t)48U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)49U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)48U * sizeof (uint8_t));
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)49U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
          }
          input[48U] = (uint8_t)1U;
          compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
          compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
          memcpy(k, k_0, (uint32_t)48U * sizeof (uint8_t));
        }
        ctr[0U] = (uint32_t)1U;
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
        state uu____3 = st;
        uint8_t *k = uu____3.k;
        uint8_t *v = uu____3.v;
        uint32_t *ctr = uu____3.reseed_counter;
        uint32_t input_len = (uint32_t)65U + entropy_input_len + additional_input_input_len;
        KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
        uint8_t input0[input_len];
        memset(input0, 0U, input_len * sizeof (uint8_t));
        uint8_t *k_ = input0;
        memcpy(k_, v, (uint32_t)64U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          memcpy(input0 + (uint32_t)65U,
            seed_material,
            (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
        }
        input0[64U] = (uint8_t)0U;
        compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
        compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
        memcpy(k, k_, (uint32_t)64U * sizeof (uint8_t));
        if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
        {
          uint32_t input_len0 = (uint32_t)65U + entropy_input_len + additional_input_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
          uint8_t input[input_len0];
          memset(input, 0U, input_len0 * sizeof (uint8_t));
          uint8_t *k_0 = input;
          memcpy(k_0, v, (uint32_t)64U * sizeof (uint8_t));
          if (entropy_input_len + additional_input_input_len != (uint32_t)0U)
          {
            memcpy(input + (uint32_t)65U,
              seed_material,
              (entropy_input_len + additional_input_input_len) * sizeof (uint8_t));
          }
          input[64U] = (uint8_t)1U;
          compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
          compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
          memcpy(k, k_0, (uint32_t)64U * sizeof (uint8_t));
        }
        ctr[0U] = (uint32_t)1U;
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
          if (additional_input_len > (uint32_t)0U)
          {
            uint32_t input_len = (uint32_t)21U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
            uint8_t input0[input_len];
            memset(input0, 0U, input_len * sizeof (uint8_t));
            uint8_t *k_ = input0;
            memcpy(k_, v, (uint32_t)20U * sizeof (uint8_t));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input0 + (uint32_t)21U,
                additional_input,
                additional_input_len * sizeof (uint8_t));
            }
            input0[20U] = (uint8_t)0U;
            legacy_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
            legacy_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
            memcpy(k, k_, (uint32_t)20U * sizeof (uint8_t));
            if (additional_input_len != (uint32_t)0U)
            {
              uint32_t input_len0 = (uint32_t)21U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
              uint8_t input[input_len0];
              memset(input, 0U, input_len0 * sizeof (uint8_t));
              uint8_t *k_0 = input;
              memcpy(k_0, v, (uint32_t)20U * sizeof (uint8_t));
              if (additional_input_len != (uint32_t)0U)
              {
                memcpy(input + (uint32_t)21U,
                  additional_input,
                  additional_input_len * sizeof (uint8_t));
              }
              input[20U] = (uint8_t)1U;
              legacy_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
              legacy_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
              memcpy(k, k_0, (uint32_t)20U * sizeof (uint8_t));
            }
          }
          uint8_t *output1 = output;
          uint32_t max = n / (uint32_t)20U;
          uint8_t *out = output1;
          for (uint32_t i = (uint32_t)0U; i < max; i++)
          {
            legacy_compute_sha1(v, k, (uint32_t)20U, v, (uint32_t)20U);
            memcpy(out + i * (uint32_t)20U, v, (uint32_t)20U * sizeof (uint8_t));
          }
          if (max * (uint32_t)20U < n)
          {
            uint8_t *block = output1 + max * (uint32_t)20U;
            legacy_compute_sha1(v, k, (uint32_t)20U, v, (uint32_t)20U);
            memcpy(block, v, (n - max * (uint32_t)20U) * sizeof (uint8_t));
          }
          uint32_t input_len = (uint32_t)21U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t input0[input_len];
          memset(input0, 0U, input_len * sizeof (uint8_t));
          uint8_t *k_ = input0;
          memcpy(k_, v, (uint32_t)20U * sizeof (uint8_t));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input0 + (uint32_t)21U,
              additional_input,
              additional_input_len * sizeof (uint8_t));
          }
          input0[20U] = (uint8_t)0U;
          legacy_compute_sha1(k_, k, (uint32_t)20U, input0, input_len);
          legacy_compute_sha1(v, k_, (uint32_t)20U, v, (uint32_t)20U);
          memcpy(k, k_, (uint32_t)20U * sizeof (uint8_t));
          if (additional_input_len != (uint32_t)0U)
          {
            uint32_t input_len0 = (uint32_t)21U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t input[input_len0];
            memset(input, 0U, input_len0 * sizeof (uint8_t));
            uint8_t *k_0 = input;
            memcpy(k_0, v, (uint32_t)20U * sizeof (uint8_t));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input + (uint32_t)21U,
                additional_input,
                additional_input_len * sizeof (uint8_t));
            }
            input[20U] = (uint8_t)1U;
            legacy_compute_sha1(k_0, k, (uint32_t)20U, input, input_len0);
            legacy_compute_sha1(v, k_0, (uint32_t)20U, v, (uint32_t)20U);
            memcpy(k, k_0, (uint32_t)20U * sizeof (uint8_t));
          }
          uint32_t old_ctr = ctr[0U];
          ctr[0U] = old_ctr + (uint32_t)1U;
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
          if (additional_input_len > (uint32_t)0U)
          {
            uint32_t input_len = (uint32_t)33U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
            uint8_t input0[input_len];
            memset(input0, 0U, input_len * sizeof (uint8_t));
            uint8_t *k_ = input0;
            memcpy(k_, v, (uint32_t)32U * sizeof (uint8_t));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input0 + (uint32_t)33U,
                additional_input,
                additional_input_len * sizeof (uint8_t));
            }
            input0[32U] = (uint8_t)0U;
            compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
            compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
            memcpy(k, k_, (uint32_t)32U * sizeof (uint8_t));
            if (additional_input_len != (uint32_t)0U)
            {
              uint32_t input_len0 = (uint32_t)33U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
              uint8_t input[input_len0];
              memset(input, 0U, input_len0 * sizeof (uint8_t));
              uint8_t *k_0 = input;
              memcpy(k_0, v, (uint32_t)32U * sizeof (uint8_t));
              if (additional_input_len != (uint32_t)0U)
              {
                memcpy(input + (uint32_t)33U,
                  additional_input,
                  additional_input_len * sizeof (uint8_t));
              }
              input[32U] = (uint8_t)1U;
              compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
              compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
              memcpy(k, k_0, (uint32_t)32U * sizeof (uint8_t));
            }
          }
          uint8_t *output1 = output;
          uint32_t max = n / (uint32_t)32U;
          uint8_t *out = output1;
          for (uint32_t i = (uint32_t)0U; i < max; i++)
          {
            compute_sha2_256(v, k, (uint32_t)32U, v, (uint32_t)32U);
            memcpy(out + i * (uint32_t)32U, v, (uint32_t)32U * sizeof (uint8_t));
          }
          if (max * (uint32_t)32U < n)
          {
            uint8_t *block = output1 + max * (uint32_t)32U;
            compute_sha2_256(v, k, (uint32_t)32U, v, (uint32_t)32U);
            memcpy(block, v, (n - max * (uint32_t)32U) * sizeof (uint8_t));
          }
          uint32_t input_len = (uint32_t)33U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t input0[input_len];
          memset(input0, 0U, input_len * sizeof (uint8_t));
          uint8_t *k_ = input0;
          memcpy(k_, v, (uint32_t)32U * sizeof (uint8_t));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input0 + (uint32_t)33U,
              additional_input,
              additional_input_len * sizeof (uint8_t));
          }
          input0[32U] = (uint8_t)0U;
          compute_sha2_256(k_, k, (uint32_t)32U, input0, input_len);
          compute_sha2_256(v, k_, (uint32_t)32U, v, (uint32_t)32U);
          memcpy(k, k_, (uint32_t)32U * sizeof (uint8_t));
          if (additional_input_len != (uint32_t)0U)
          {
            uint32_t input_len0 = (uint32_t)33U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t input[input_len0];
            memset(input, 0U, input_len0 * sizeof (uint8_t));
            uint8_t *k_0 = input;
            memcpy(k_0, v, (uint32_t)32U * sizeof (uint8_t));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input + (uint32_t)33U,
                additional_input,
                additional_input_len * sizeof (uint8_t));
            }
            input[32U] = (uint8_t)1U;
            compute_sha2_256(k_0, k, (uint32_t)32U, input, input_len0);
            compute_sha2_256(v, k_0, (uint32_t)32U, v, (uint32_t)32U);
            memcpy(k, k_0, (uint32_t)32U * sizeof (uint8_t));
          }
          uint32_t old_ctr = ctr[0U];
          ctr[0U] = old_ctr + (uint32_t)1U;
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
          if (additional_input_len > (uint32_t)0U)
          {
            uint32_t input_len = (uint32_t)49U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
            uint8_t input0[input_len];
            memset(input0, 0U, input_len * sizeof (uint8_t));
            uint8_t *k_ = input0;
            memcpy(k_, v, (uint32_t)48U * sizeof (uint8_t));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input0 + (uint32_t)49U,
                additional_input,
                additional_input_len * sizeof (uint8_t));
            }
            input0[48U] = (uint8_t)0U;
            compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
            compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
            memcpy(k, k_, (uint32_t)48U * sizeof (uint8_t));
            if (additional_input_len != (uint32_t)0U)
            {
              uint32_t input_len0 = (uint32_t)49U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
              uint8_t input[input_len0];
              memset(input, 0U, input_len0 * sizeof (uint8_t));
              uint8_t *k_0 = input;
              memcpy(k_0, v, (uint32_t)48U * sizeof (uint8_t));
              if (additional_input_len != (uint32_t)0U)
              {
                memcpy(input + (uint32_t)49U,
                  additional_input,
                  additional_input_len * sizeof (uint8_t));
              }
              input[48U] = (uint8_t)1U;
              compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
              compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
              memcpy(k, k_0, (uint32_t)48U * sizeof (uint8_t));
            }
          }
          uint8_t *output1 = output;
          uint32_t max = n / (uint32_t)48U;
          uint8_t *out = output1;
          for (uint32_t i = (uint32_t)0U; i < max; i++)
          {
            compute_sha2_384(v, k, (uint32_t)48U, v, (uint32_t)48U);
            memcpy(out + i * (uint32_t)48U, v, (uint32_t)48U * sizeof (uint8_t));
          }
          if (max * (uint32_t)48U < n)
          {
            uint8_t *block = output1 + max * (uint32_t)48U;
            compute_sha2_384(v, k, (uint32_t)48U, v, (uint32_t)48U);
            memcpy(block, v, (n - max * (uint32_t)48U) * sizeof (uint8_t));
          }
          uint32_t input_len = (uint32_t)49U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t input0[input_len];
          memset(input0, 0U, input_len * sizeof (uint8_t));
          uint8_t *k_ = input0;
          memcpy(k_, v, (uint32_t)48U * sizeof (uint8_t));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input0 + (uint32_t)49U,
              additional_input,
              additional_input_len * sizeof (uint8_t));
          }
          input0[48U] = (uint8_t)0U;
          compute_sha2_384(k_, k, (uint32_t)48U, input0, input_len);
          compute_sha2_384(v, k_, (uint32_t)48U, v, (uint32_t)48U);
          memcpy(k, k_, (uint32_t)48U * sizeof (uint8_t));
          if (additional_input_len != (uint32_t)0U)
          {
            uint32_t input_len0 = (uint32_t)49U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t input[input_len0];
            memset(input, 0U, input_len0 * sizeof (uint8_t));
            uint8_t *k_0 = input;
            memcpy(k_0, v, (uint32_t)48U * sizeof (uint8_t));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input + (uint32_t)49U,
                additional_input,
                additional_input_len * sizeof (uint8_t));
            }
            input[48U] = (uint8_t)1U;
            compute_sha2_384(k_0, k, (uint32_t)48U, input, input_len0);
            compute_sha2_384(v, k_0, (uint32_t)48U, v, (uint32_t)48U);
            memcpy(k, k_0, (uint32_t)48U * sizeof (uint8_t));
          }
          uint32_t old_ctr = ctr[0U];
          ctr[0U] = old_ctr + (uint32_t)1U;
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
          if (additional_input_len > (uint32_t)0U)
          {
            uint32_t input_len = (uint32_t)65U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
            uint8_t input0[input_len];
            memset(input0, 0U, input_len * sizeof (uint8_t));
            uint8_t *k_ = input0;
            memcpy(k_, v, (uint32_t)64U * sizeof (uint8_t));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input0 + (uint32_t)65U,
                additional_input,
                additional_input_len * sizeof (uint8_t));
            }
            input0[64U] = (uint8_t)0U;
            compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
            compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
            memcpy(k, k_, (uint32_t)64U * sizeof (uint8_t));
            if (additional_input_len != (uint32_t)0U)
            {
              uint32_t input_len0 = (uint32_t)65U + additional_input_len;
              KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
              uint8_t input[input_len0];
              memset(input, 0U, input_len0 * sizeof (uint8_t));
              uint8_t *k_0 = input;
              memcpy(k_0, v, (uint32_t)64U * sizeof (uint8_t));
              if (additional_input_len != (uint32_t)0U)
              {
                memcpy(input + (uint32_t)65U,
                  additional_input,
                  additional_input_len * sizeof (uint8_t));
              }
              input[64U] = (uint8_t)1U;
              compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
              compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
              memcpy(k, k_0, (uint32_t)64U * sizeof (uint8_t));
            }
          }
          uint8_t *output1 = output;
          uint32_t max = n / (uint32_t)64U;
          uint8_t *out = output1;
          for (uint32_t i = (uint32_t)0U; i < max; i++)
          {
            compute_sha2_512(v, k, (uint32_t)64U, v, (uint32_t)64U);
            memcpy(out + i * (uint32_t)64U, v, (uint32_t)64U * sizeof (uint8_t));
          }
          if (max * (uint32_t)64U < n)
          {
            uint8_t *block = output1 + max * (uint32_t)64U;
            compute_sha2_512(v, k, (uint32_t)64U, v, (uint32_t)64U);
            memcpy(block, v, (n - max * (uint32_t)64U) * sizeof (uint8_t));
          }
          uint32_t input_len = (uint32_t)65U + additional_input_len;
          KRML_CHECK_SIZE(sizeof (uint8_t), input_len);
          uint8_t input0[input_len];
          memset(input0, 0U, input_len * sizeof (uint8_t));
          uint8_t *k_ = input0;
          memcpy(k_, v, (uint32_t)64U * sizeof (uint8_t));
          if (additional_input_len != (uint32_t)0U)
          {
            memcpy(input0 + (uint32_t)65U,
              additional_input,
              additional_input_len * sizeof (uint8_t));
          }
          input0[64U] = (uint8_t)0U;
          compute_sha2_512(k_, k, (uint32_t)64U, input0, input_len);
          compute_sha2_512(v, k_, (uint32_t)64U, v, (uint32_t)64U);
          memcpy(k, k_, (uint32_t)64U * sizeof (uint8_t));
          if (additional_input_len != (uint32_t)0U)
          {
            uint32_t input_len0 = (uint32_t)65U + additional_input_len;
            KRML_CHECK_SIZE(sizeof (uint8_t), input_len0);
            uint8_t input[input_len0];
            memset(input, 0U, input_len0 * sizeof (uint8_t));
            uint8_t *k_0 = input;
            memcpy(k_0, v, (uint32_t)64U * sizeof (uint8_t));
            if (additional_input_len != (uint32_t)0U)
            {
              memcpy(input + (uint32_t)65U,
                additional_input,
                additional_input_len * sizeof (uint8_t));
            }
            input[64U] = (uint8_t)1U;
            compute_sha2_512(k_0, k, (uint32_t)64U, input, input_len0);
            compute_sha2_512(v, k_0, (uint32_t)64U, v, (uint32_t)64U);
            memcpy(k, k_0, (uint32_t)64U * sizeof (uint8_t));
          }
          uint32_t old_ctr = ctr[0U];
          ctr[0U] = old_ctr + (uint32_t)1U;
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
  {
    (uint8_t)124U, (uint8_t)173U, (uint8_t)101U, (uint8_t)229U, (uint8_t)204U, (uint8_t)40U,
    (uint8_t)136U, (uint8_t)174U, (uint8_t)78U, (uint8_t)150U, (uint8_t)15U, (uint8_t)93U,
    (uint8_t)20U, (uint8_t)60U, (uint8_t)20U, (uint8_t)37U
  };

static uint8_t
vectors_low1[8U] =
  {
    (uint8_t)252U, (uint8_t)7U, (uint8_t)133U, (uint8_t)219U, (uint8_t)71U, (uint8_t)28U,
    (uint8_t)197U, (uint8_t)94U
  };

static uint8_t
vectors_low2[16U] =
  {
    (uint8_t)102U, (uint8_t)69U, (uint8_t)29U, (uint8_t)41U, (uint8_t)207U, (uint8_t)101U,
    (uint8_t)216U, (uint8_t)153U, (uint8_t)162U, (uint8_t)129U, (uint8_t)144U, (uint8_t)95U,
    (uint8_t)249U, (uint8_t)178U, (uint8_t)158U, (uint8_t)135U
  };

static uint8_t
vectors_low3[16U] =
  {
    (uint8_t)128U, (uint8_t)13U, (uint8_t)88U, (uint8_t)59U, (uint8_t)37U, (uint8_t)96U,
    (uint8_t)210U, (uint8_t)162U, (uint8_t)48U, (uint8_t)1U, (uint8_t)50U, (uint8_t)238U,
    (uint8_t)45U, (uint8_t)19U, (uint8_t)241U, (uint8_t)159U
  };

static uint8_t
vectors_low4[16U] =
  {
    (uint8_t)66U, (uint8_t)234U, (uint8_t)231U, (uint8_t)5U, (uint8_t)194U, (uint8_t)34U,
    (uint8_t)93U, (uint8_t)33U, (uint8_t)47U, (uint8_t)160U, (uint8_t)85U, (uint8_t)74U,
    (uint8_t)198U, (uint8_t)172U, (uint8_t)86U, (uint8_t)75U
  };

static uint8_t
vectors_low5[16U] =
  {
    (uint8_t)114U, (uint8_t)8U, (uint8_t)30U, (uint8_t)126U, (uint8_t)112U, (uint8_t)32U,
    (uint8_t)15U, (uint8_t)25U, (uint8_t)130U, (uint8_t)195U, (uint8_t)173U, (uint8_t)156U,
    (uint8_t)177U, (uint8_t)211U, (uint8_t)221U, (uint8_t)190U
  };

static uint8_t
vectors_low6[80U] =
  {
    (uint8_t)149U, (uint8_t)62U, (uint8_t)146U, (uint8_t)37U, (uint8_t)139U, (uint8_t)231U,
    (uint8_t)255U, (uint8_t)97U, (uint8_t)185U, (uint8_t)112U, (uint8_t)119U, (uint8_t)37U,
    (uint8_t)42U, (uint8_t)185U, (uint8_t)131U, (uint8_t)82U, (uint8_t)49U, (uint8_t)227U,
    (uint8_t)102U, (uint8_t)223U, (uint8_t)165U, (uint8_t)182U, (uint8_t)53U, (uint8_t)251U,
    (uint8_t)136U, (uint8_t)156U, (uint8_t)51U, (uint8_t)117U, (uint8_t)98U, (uint8_t)162U,
    (uint8_t)100U, (uint8_t)29U, (uint8_t)58U, (uint8_t)169U, (uint8_t)228U, (uint8_t)111U,
    (uint8_t)238U, (uint8_t)178U, (uint8_t)164U, (uint8_t)234U, (uint8_t)3U, (uint8_t)203U,
    (uint8_t)115U, (uint8_t)241U, (uint8_t)248U, (uint8_t)1U, (uint8_t)89U, (uint8_t)76U,
    (uint8_t)60U, (uint8_t)199U, (uint8_t)29U, (uint8_t)41U, (uint8_t)69U, (uint8_t)193U,
    (uint8_t)26U, (uint8_t)82U, (uint8_t)187U, (uint8_t)14U, (uint8_t)147U, (uint8_t)65U,
    (uint8_t)157U, (uint8_t)245U, (uint8_t)208U, (uint8_t)133U, (uint8_t)74U, (uint8_t)213U,
    (uint8_t)242U, (uint8_t)227U, (uint8_t)109U, (uint8_t)34U, (uint8_t)60U, (uint8_t)17U,
    (uint8_t)158U, (uint8_t)20U, (uint8_t)92U, (uint8_t)173U, (uint8_t)80U, (uint8_t)116U,
    (uint8_t)149U, (uint8_t)167U
  };

static uint8_t
vectors_low7[16U] =
  {
    (uint8_t)7U, (uint8_t)54U, (uint8_t)160U, (uint8_t)131U, (uint8_t)89U, (uint8_t)90U,
    (uint8_t)131U, (uint8_t)151U, (uint8_t)203U, (uint8_t)158U, (uint8_t)103U, (uint8_t)108U,
    (uint8_t)179U, (uint8_t)123U, (uint8_t)251U, (uint8_t)90U
  };

static uint8_t
vectors_low8[8U] =
  {
    (uint8_t)11U, (uint8_t)24U, (uint8_t)74U, (uint8_t)109U, (uint8_t)10U, (uint8_t)99U,
    (uint8_t)10U, (uint8_t)187U
  };

static uint8_t
vectors_low9[16U] =
  {
    (uint8_t)195U, (uint8_t)2U, (uint8_t)80U, (uint8_t)61U, (uint8_t)134U, (uint8_t)162U,
    (uint8_t)189U, (uint8_t)228U, (uint8_t)106U, (uint8_t)12U, (uint8_t)99U, (uint8_t)86U,
    (uint8_t)26U, (uint8_t)134U, (uint8_t)207U, (uint8_t)217U
  };

static uint8_t
vectors_low10[16U] =
  {
    (uint8_t)75U, (uint8_t)80U, (uint8_t)151U, (uint8_t)112U, (uint8_t)51U, (uint8_t)72U,
    (uint8_t)50U, (uint8_t)119U, (uint8_t)100U, (uint8_t)121U, (uint8_t)69U, (uint8_t)255U,
    (uint8_t)239U, (uint8_t)161U, (uint8_t)9U, (uint8_t)226U
  };

static uint8_t
vectors_low11[16U] =
  {
    (uint8_t)77U, (uint8_t)173U, (uint8_t)129U, (uint8_t)55U, (uint8_t)68U, (uint8_t)245U,
    (uint8_t)67U, (uint8_t)36U, (uint8_t)179U, (uint8_t)4U, (uint8_t)106U, (uint8_t)133U,
    (uint8_t)190U, (uint8_t)60U, (uint8_t)195U, (uint8_t)200U
  };

static uint8_t
vectors_low12[16U] =
  {
    (uint8_t)116U, (uint8_t)65U, (uint8_t)254U, (uint8_t)250U, (uint8_t)96U, (uint8_t)247U,
    (uint8_t)238U, (uint8_t)72U, (uint8_t)255U, (uint8_t)56U, (uint8_t)123U, (uint8_t)88U,
    (uint8_t)126U, (uint8_t)252U, (uint8_t)179U, (uint8_t)230U
  };

static uint8_t
vectors_low13[16U] =
  {
    (uint8_t)240U, (uint8_t)208U, (uint8_t)5U, (uint8_t)40U, (uint8_t)154U, (uint8_t)157U,
    (uint8_t)57U, (uint8_t)147U, (uint8_t)196U, (uint8_t)75U, (uint8_t)183U, (uint8_t)80U,
    (uint8_t)217U, (uint8_t)108U, (uint8_t)193U, (uint8_t)188U
  };

static uint8_t
vectors_low14[80U] =
  {
    (uint8_t)192U, (uint8_t)57U, (uint8_t)113U, (uint8_t)137U, (uint8_t)123U, (uint8_t)133U,
    (uint8_t)69U, (uint8_t)133U, (uint8_t)153U, (uint8_t)78U, (uint8_t)235U, (uint8_t)142U,
    (uint8_t)61U, (uint8_t)107U, (uint8_t)85U, (uint8_t)110U, (uint8_t)26U, (uint8_t)141U,
    (uint8_t)241U, (uint8_t)138U, (uint8_t)127U, (uint8_t)248U, (uint8_t)143U, (uint8_t)131U,
    (uint8_t)232U, (uint8_t)254U, (uint8_t)23U, (uint8_t)230U, (uint8_t)221U, (uint8_t)144U,
    (uint8_t)113U, (uint8_t)7U, (uint8_t)10U, (uint8_t)109U, (uint8_t)190U, (uint8_t)246U,
    (uint8_t)124U, (uint8_t)182U, (uint8_t)18U, (uint8_t)172U, (uint8_t)241U, (uint8_t)34U,
    (uint8_t)202U, (uint8_t)167U, (uint8_t)248U, (uint8_t)23U, (uint8_t)112U, (uint8_t)75U,
    (uint8_t)62U, (uint8_t)252U, (uint8_t)110U, (uint8_t)27U, (uint8_t)31U, (uint8_t)214U,
    (uint8_t)195U, (uint8_t)48U, (uint8_t)224U, (uint8_t)167U, (uint8_t)50U, (uint8_t)171U,
    (uint8_t)234U, (uint8_t)147U, (uint8_t)192U, (uint8_t)8U, (uint8_t)24U, (uint8_t)225U,
    (uint8_t)44U, (uint8_t)80U, (uint8_t)79U, (uint8_t)216U, (uint8_t)224U, (uint8_t)179U,
    (uint8_t)108U, (uint8_t)136U, (uint8_t)248U, (uint8_t)74U, (uint8_t)149U, (uint8_t)180U,
    (uint8_t)147U, (uint8_t)98U
  };

static uint8_t
vectors_low15[16U] =
  {
    (uint8_t)23U, (uint8_t)32U, (uint8_t)84U, (uint8_t)200U, (uint8_t)39U, (uint8_t)170U,
    (uint8_t)137U, (uint8_t)95U, (uint8_t)161U, (uint8_t)35U, (uint8_t)155U, (uint8_t)122U,
    (uint8_t)72U, (uint8_t)71U, (uint8_t)82U, (uint8_t)242U
  };

static uint8_t
vectors_low16[8U] =
  {
    (uint8_t)237U, (uint8_t)178U, (uint8_t)114U, (uint8_t)192U, (uint8_t)169U, (uint8_t)140U,
    (uint8_t)117U, (uint8_t)146U
  };

static uint8_t
vectors_low17[16U] =
  {
    (uint8_t)71U, (uint8_t)188U, (uint8_t)120U, (uint8_t)191U, (uint8_t)189U, (uint8_t)27U,
    (uint8_t)183U, (uint8_t)226U, (uint8_t)220U, (uint8_t)219U, (uint8_t)244U, (uint8_t)235U,
    (uint8_t)228U, (uint8_t)44U, (uint8_t)82U, (uint8_t)147U
  };

static uint8_t
vectors_low18[16U] =
  {
    (uint8_t)41U, (uint8_t)249U, (uint8_t)42U, (uint8_t)14U, (uint8_t)93U, (uint8_t)36U,
    (uint8_t)225U, (uint8_t)154U, (uint8_t)246U, (uint8_t)152U, (uint8_t)135U, (uint8_t)127U,
    (uint8_t)105U, (uint8_t)160U, (uint8_t)239U, (uint8_t)181U
  };

static uint8_t
vectors_low19[80U] =
  {
    (uint8_t)100U, (uint8_t)100U, (uint8_t)189U, (uint8_t)174U, (uint8_t)210U, (uint8_t)50U,
    (uint8_t)69U, (uint8_t)219U, (uint8_t)31U, (uint8_t)101U, (uint8_t)16U, (uint8_t)248U,
    (uint8_t)101U, (uint8_t)158U, (uint8_t)27U, (uint8_t)25U, (uint8_t)136U, (uint8_t)29U,
    (uint8_t)96U, (uint8_t)98U, (uint8_t)32U, (uint8_t)153U, (uint8_t)123U, (uint8_t)131U,
    (uint8_t)118U, (uint8_t)132U, (uint8_t)167U, (uint8_t)248U, (uint8_t)138U, (uint8_t)22U,
    (uint8_t)108U, (uint8_t)183U, (uint8_t)92U, (uint8_t)230U, (uint8_t)130U, (uint8_t)156U,
    (uint8_t)179U, (uint8_t)241U, (uint8_t)30U, (uint8_t)85U, (uint8_t)210U, (uint8_t)183U,
    (uint8_t)173U, (uint8_t)52U, (uint8_t)156U, (uint8_t)193U, (uint8_t)244U, (uint8_t)186U,
    (uint8_t)2U, (uint8_t)227U, (uint8_t)10U, (uint8_t)118U, (uint8_t)249U, (uint8_t)112U,
    (uint8_t)97U, (uint8_t)58U, (uint8_t)167U, (uint8_t)70U, (uint8_t)53U, (uint8_t)176U,
    (uint8_t)3U, (uint8_t)79U, (uint8_t)142U, (uint8_t)152U, (uint8_t)92U, (uint8_t)222U,
    (uint8_t)79U, (uint8_t)31U, (uint8_t)221U, (uint8_t)185U, (uint8_t)100U, (uint8_t)101U,
    (uint8_t)122U, (uint8_t)22U, (uint8_t)147U, (uint8_t)134U, (uint8_t)226U, (uint8_t)7U,
    (uint8_t)103U, (uint8_t)209U
  };

static uint8_t
vectors_low20[16U] =
  {
    (uint8_t)177U, (uint8_t)161U, (uint8_t)155U, (uint8_t)176U, (uint8_t)124U, (uint8_t)48U,
    (uint8_t)202U, (uint8_t)79U, (uint8_t)73U, (uint8_t)220U, (uint8_t)105U, (uint8_t)19U,
    (uint8_t)13U, (uint8_t)35U, (uint8_t)192U, (uint8_t)167U
  };

static uint8_t
vectors_low21[8U] =
  {
    (uint8_t)44U, (uint8_t)6U, (uint8_t)6U, (uint8_t)114U, (uint8_t)151U, (uint8_t)5U,
    (uint8_t)142U, (uint8_t)197U
  };

static uint8_t
vectors_low22[16U] =
  {
    (uint8_t)132U, (uint8_t)8U, (uint8_t)2U, (uint8_t)206U, (uint8_t)162U, (uint8_t)229U,
    (uint8_t)90U, (uint8_t)59U, (uint8_t)30U, (uint8_t)72U, (uint8_t)123U, (uint8_t)183U,
    (uint8_t)174U, (uint8_t)230U, (uint8_t)43U, (uint8_t)66U
  };

static uint8_t
vectors_low23[80U] =
  {
    (uint8_t)244U, (uint8_t)27U, (uint8_t)183U, (uint8_t)174U, (uint8_t)83U, (uint8_t)35U,
    (uint8_t)68U, (uint8_t)169U, (uint8_t)13U, (uint8_t)65U, (uint8_t)59U, (uint8_t)102U,
    (uint8_t)169U, (uint8_t)78U, (uint8_t)225U, (uint8_t)208U, (uint8_t)37U, (uint8_t)74U,
    (uint8_t)93U, (uint8_t)94U, (uint8_t)151U, (uint8_t)78U, (uint8_t)54U, (uint8_t)177U,
    (uint8_t)153U, (uint8_t)59U, (uint8_t)16U, (uint8_t)66U, (uint8_t)88U, (uint8_t)111U,
    (uint8_t)84U, (uint8_t)114U, (uint8_t)141U, (uint8_t)30U, (uint8_t)187U, (uint8_t)124U,
    (uint8_t)93U, (uint8_t)53U, (uint8_t)21U, (uint8_t)88U, (uint8_t)237U, (uint8_t)103U,
    (uint8_t)81U, (uint8_t)119U, (uint8_t)228U, (uint8_t)50U, (uint8_t)54U, (uint8_t)7U,
    (uint8_t)8U, (uint8_t)192U, (uint8_t)8U, (uint8_t)152U, (uint8_t)76U, (uint8_t)65U,
    (uint8_t)188U, (uint8_t)76U, (uint8_t)130U, (uint8_t)141U, (uint8_t)131U, (uint8_t)221U,
    (uint8_t)236U, (uint8_t)169U, (uint8_t)239U, (uint8_t)142U, (uint8_t)205U, (uint8_t)157U,
    (uint8_t)168U, (uint8_t)128U, (uint8_t)161U, (uint8_t)53U, (uint8_t)64U, (uint8_t)10U,
    (uint8_t)67U, (uint8_t)249U, (uint8_t)31U, (uint8_t)76U, (uint8_t)166U, (uint8_t)213U,
    (uint8_t)157U
  };

static uint8_t
vectors_low24[16U] =
  {
    (uint8_t)52U, (uint8_t)63U, (uint8_t)157U, (uint8_t)222U, (uint8_t)137U, (uint8_t)169U,
    (uint8_t)227U, (uint8_t)236U, (uint8_t)196U, (uint8_t)249U, (uint8_t)101U, (uint8_t)60U,
    (uint8_t)139U, (uint8_t)57U, (uint8_t)45U, (uint8_t)171U
  };

static uint8_t
vectors_low25[8U] =
  {
    (uint8_t)196U, (uint8_t)251U, (uint8_t)54U, (uint8_t)6U, (uint8_t)216U, (uint8_t)246U,
    (uint8_t)45U, (uint8_t)177U
  };

static uint8_t
vectors_low26[16U] =
  {
    (uint8_t)2U, (uint8_t)31U, (uint8_t)195U, (uint8_t)234U, (uint8_t)212U, (uint8_t)111U,
    (uint8_t)248U, (uint8_t)189U, (uint8_t)163U, (uint8_t)183U, (uint8_t)151U, (uint8_t)1U,
    (uint8_t)183U, (uint8_t)137U, (uint8_t)58U, (uint8_t)57U
  };

static uint8_t
vectors_low27[16U] =
  {
    (uint8_t)137U, (uint8_t)24U, (uint8_t)131U, (uint8_t)30U, (uint8_t)21U, (uint8_t)212U,
    (uint8_t)48U, (uint8_t)97U, (uint8_t)111U, (uint8_t)75U, (uint8_t)217U, (uint8_t)16U,
    (uint8_t)70U, (uint8_t)254U, (uint8_t)9U, (uint8_t)48U
  };

static uint8_t
vectors_low28[16U] =
  {
    (uint8_t)168U, (uint8_t)119U, (uint8_t)35U, (uint8_t)4U, (uint8_t)161U, (uint8_t)172U,
    (uint8_t)203U, (uint8_t)22U, (uint8_t)102U, (uint8_t)34U, (uint8_t)24U, (uint8_t)167U,
    (uint8_t)72U, (uint8_t)187U, (uint8_t)79U, (uint8_t)216U
  };

static uint8_t
vectors_low29[16U] =
  {
    (uint8_t)75U, (uint8_t)249U, (uint8_t)242U, (uint8_t)185U, (uint8_t)209U, (uint8_t)94U,
    (uint8_t)195U, (uint8_t)7U, (uint8_t)31U, (uint8_t)243U, (uint8_t)103U, (uint8_t)74U,
    (uint8_t)215U, (uint8_t)65U, (uint8_t)135U, (uint8_t)89U
  };

static uint8_t
vectors_low30[80U] =
  {
    (uint8_t)151U, (uint8_t)130U, (uint8_t)178U, (uint8_t)17U, (uint8_t)28U, (uint8_t)152U,
    (uint8_t)91U, (uint8_t)202U, (uint8_t)171U, (uint8_t)11U, (uint8_t)137U, (uint8_t)5U,
    (uint8_t)173U, (uint8_t)155U, (uint8_t)203U, (uint8_t)151U, (uint8_t)235U, (uint8_t)63U,
    (uint8_t)53U, (uint8_t)84U, (uint8_t)198U, (uint8_t)141U, (uint8_t)121U, (uint8_t)238U,
    (uint8_t)92U, (uint8_t)161U, (uint8_t)220U, (uint8_t)251U, (uint8_t)208U, (uint8_t)215U,
    (uint8_t)133U, (uint8_t)15U, (uint8_t)101U, (uint8_t)9U, (uint8_t)12U, (uint8_t)121U,
    (uint8_t)210U, (uint8_t)29U, (uint8_t)28U, (uint8_t)98U, (uint8_t)83U, (uint8_t)207U,
    (uint8_t)73U, (uint8_t)63U, (uint8_t)8U, (uint8_t)57U, (uint8_t)44U, (uint8_t)251U,
    (uint8_t)96U, (uint8_t)70U, (uint8_t)31U, (uint8_t)188U, (uint8_t)32U, (uint8_t)190U,
    (uint8_t)180U, (uint8_t)207U, (uint8_t)62U, (uint8_t)2U, (uint8_t)33U, (uint8_t)35U,
    (uint8_t)129U, (uint8_t)111U, (uint8_t)11U, (uint8_t)197U, (uint8_t)151U, (uint8_t)171U,
    (uint8_t)235U, (uint8_t)199U, (uint8_t)117U, (uint8_t)99U, (uint8_t)61U, (uint8_t)179U,
    (uint8_t)36U, (uint8_t)199U, (uint8_t)193U, (uint8_t)199U, (uint8_t)205U, (uint8_t)94U,
    (uint8_t)140U, (uint8_t)86U
  };

static uint8_t
vectors_low31[16U] =
  {
    (uint8_t)10U, (uint8_t)8U, (uint8_t)103U, (uint8_t)38U, (uint8_t)246U, (uint8_t)111U,
    (uint8_t)42U, (uint8_t)201U, (uint8_t)231U, (uint8_t)218U, (uint8_t)166U, (uint8_t)25U,
    (uint8_t)8U, (uint8_t)246U, (uint8_t)51U, (uint8_t)25U
  };

static uint8_t
vectors_low32[8U] =
  {
    (uint8_t)222U, (uint8_t)191U, (uint8_t)1U, (uint8_t)29U, (uint8_t)64U, (uint8_t)106U,
    (uint8_t)91U, (uint8_t)35U
  };

static uint8_t
vectors_low33[16U] =
  {
    (uint8_t)88U, (uint8_t)88U, (uint8_t)45U, (uint8_t)167U, (uint8_t)79U, (uint8_t)143U,
    (uint8_t)145U, (uint8_t)219U, (uint8_t)4U, (uint8_t)68U, (uint8_t)190U, (uint8_t)174U,
    (uint8_t)57U, (uint8_t)1U, (uint8_t)104U, (uint8_t)87U
  };

static uint8_t
vectors_low34[16U] =
  {
    (uint8_t)201U, (uint8_t)43U, (uint8_t)162U, (uint8_t)144U, (uint8_t)10U, (uint8_t)176U,
    (uint8_t)164U, (uint8_t)202U, (uint8_t)53U, (uint8_t)83U, (uint8_t)128U, (uint8_t)99U,
    (uint8_t)146U, (uint8_t)182U, (uint8_t)179U, (uint8_t)229U
  };

static uint8_t
vectors_low35[16U] =
  {
    (uint8_t)86U, (uint8_t)4U, (uint8_t)167U, (uint8_t)110U, (uint8_t)116U, (uint8_t)239U,
    (uint8_t)75U, (uint8_t)48U, (uint8_t)68U, (uint8_t)102U, (uint8_t)242U, (uint8_t)29U,
    (uint8_t)245U, (uint8_t)124U, (uint8_t)112U, (uint8_t)243U
  };

static uint8_t
vectors_low36[16U] =
  {
    (uint8_t)225U, (uint8_t)228U, (uint8_t)208U, (uint8_t)117U, (uint8_t)76U, (uint8_t)195U,
    (uint8_t)6U, (uint8_t)161U, (uint8_t)117U, (uint8_t)43U, (uint8_t)80U, (uint8_t)197U,
    (uint8_t)196U, (uint8_t)70U, (uint8_t)163U, (uint8_t)208U
  };

static uint8_t
vectors_low37[16U] =
  {
    (uint8_t)113U, (uint8_t)218U, (uint8_t)207U, (uint8_t)97U, (uint8_t)135U, (uint8_t)92U,
    (uint8_t)191U, (uint8_t)54U, (uint8_t)85U, (uint8_t)228U, (uint8_t)247U, (uint8_t)210U,
    (uint8_t)224U, (uint8_t)129U, (uint8_t)212U, (uint8_t)147U
  };

static uint8_t
vectors_low38[80U] =
  {
    (uint8_t)175U, (uint8_t)187U, (uint8_t)58U, (uint8_t)5U, (uint8_t)231U, (uint8_t)83U,
    (uint8_t)246U, (uint8_t)235U, (uint8_t)240U, (uint8_t)38U, (uint8_t)89U, (uint8_t)74U,
    (uint8_t)3U, (uint8_t)178U, (uint8_t)43U, (uint8_t)63U, (uint8_t)3U, (uint8_t)46U,
    (uint8_t)219U, (uint8_t)135U, (uint8_t)59U, (uint8_t)158U, (uint8_t)30U, (uint8_t)34U,
    (uint8_t)83U, (uint8_t)46U, (uint8_t)54U, (uint8_t)10U, (uint8_t)9U, (uint8_t)125U,
    (uint8_t)126U, (uint8_t)13U, (uint8_t)69U, (uint8_t)133U, (uint8_t)187U, (uint8_t)248U,
    (uint8_t)47U, (uint8_t)155U, (uint8_t)18U, (uint8_t)215U, (uint8_t)168U, (uint8_t)134U,
    (uint8_t)48U, (uint8_t)239U, (uint8_t)202U, (uint8_t)222U, (uint8_t)184U, (uint8_t)255U,
    (uint8_t)220U, (uint8_t)139U, (uint8_t)124U, (uint8_t)138U, (uint8_t)83U, (uint8_t)254U,
    (uint8_t)148U, (uint8_t)238U, (uint8_t)169U, (uint8_t)210U, (uint8_t)205U, (uint8_t)108U,
    (uint8_t)249U, (uint8_t)8U, (uint8_t)40U, (uint8_t)195U, (uint8_t)81U, (uint8_t)31U,
    (uint8_t)201U, (uint8_t)54U, (uint8_t)34U, (uint8_t)43U, (uint8_t)168U, (uint8_t)69U,
    (uint8_t)252U, (uint8_t)119U, (uint8_t)153U, (uint8_t)90U, (uint8_t)3U, (uint8_t)133U,
    (uint8_t)85U, (uint8_t)120U
  };

static uint8_t
vectors_low39[32U] =
  {
    (uint8_t)20U, (uint8_t)104U, (uint8_t)62U, (uint8_t)197U, (uint8_t)8U, (uint8_t)162U,
    (uint8_t)157U, (uint8_t)120U, (uint8_t)18U, (uint8_t)224U, (uint8_t)240U, (uint8_t)74U,
    (uint8_t)62U, (uint8_t)157U, (uint8_t)135U, (uint8_t)137U, (uint8_t)112U, (uint8_t)0U,
    (uint8_t)220U, (uint8_t)7U, (uint8_t)180U, (uint8_t)251U, (uint8_t)207U, (uint8_t)218U,
    (uint8_t)88U, (uint8_t)235U, (uint8_t)124U, (uint8_t)218U, (uint8_t)188U, (uint8_t)73U,
    (uint8_t)46U, (uint8_t)88U
  };

static uint8_t
vectors_low40[16U] =
  {
    (uint8_t)178U, (uint8_t)36U, (uint8_t)62U, (uint8_t)116U, (uint8_t)78U, (uint8_t)185U,
    (uint8_t)128U, (uint8_t)179U, (uint8_t)236U, (uint8_t)226U, (uint8_t)92U, (uint8_t)231U,
    (uint8_t)99U, (uint8_t)131U, (uint8_t)253U, (uint8_t)70U
  };

static uint8_t
vectors_low41[32U] =
  {
    (uint8_t)24U, (uint8_t)89U, (uint8_t)14U, (uint8_t)14U, (uint8_t)244U, (uint8_t)238U,
    (uint8_t)43U, (uint8_t)218U, (uint8_t)228U, (uint8_t)98U, (uint8_t)247U, (uint8_t)109U,
    (uint8_t)147U, (uint8_t)36U, (uint8_t)179U, (uint8_t)0U, (uint8_t)37U, (uint8_t)89U,
    (uint8_t)247U, (uint8_t)76U, (uint8_t)55U, (uint8_t)12U, (uint8_t)252U, (uint8_t)207U,
    (uint8_t)150U, (uint8_t)165U, (uint8_t)113U, (uint8_t)214U, (uint8_t)149U, (uint8_t)87U,
    (uint8_t)3U, (uint8_t)167U
  };

static uint8_t
vectors_low42[32U] =
  {
    (uint8_t)158U, (uint8_t)163U, (uint8_t)204U, (uint8_t)202U, (uint8_t)30U, (uint8_t)141U,
    (uint8_t)121U, (uint8_t)29U, (uint8_t)34U, (uint8_t)252U, (uint8_t)218U, (uint8_t)98U,
    (uint8_t)31U, (uint8_t)196U, (uint8_t)213U, (uint8_t)27U, (uint8_t)136U, (uint8_t)45U,
    (uint8_t)243U, (uint8_t)45U, (uint8_t)148U, (uint8_t)234U, (uint8_t)143U, (uint8_t)32U,
    (uint8_t)238U, (uint8_t)68U, (uint8_t)147U, (uint8_t)19U, (uint8_t)230U, (uint8_t)144U,
    (uint8_t)155U, (uint8_t)120U
  };

static uint8_t
vectors_low43[32U] =
  {
    (uint8_t)22U, (uint8_t)54U, (uint8_t)106U, (uint8_t)87U, (uint8_t)139U, (uint8_t)94U,
    (uint8_t)164U, (uint8_t)208U, (uint8_t)203U, (uint8_t)84U, (uint8_t)119U, (uint8_t)144U,
    (uint8_t)239U, (uint8_t)91U, (uint8_t)79U, (uint8_t)212U, (uint8_t)93U, (uint8_t)124U,
    (uint8_t)216U, (uint8_t)69U, (uint8_t)188U, (uint8_t)138U, (uint8_t)124U, (uint8_t)69U,
    (uint8_t)233U, (uint8_t)148U, (uint8_t)25U, (uint8_t)200U, (uint8_t)115U, (uint8_t)125U,
    (uint8_t)235U, (uint8_t)180U
  };

static uint8_t
vectors_low44[32U] =
  {
    (uint8_t)166U, (uint8_t)140U, (uint8_t)170U, (uint8_t)41U, (uint8_t)165U, (uint8_t)63U,
    (uint8_t)27U, (uint8_t)168U, (uint8_t)87U, (uint8_t)228U, (uint8_t)132U, (uint8_t)208U,
    (uint8_t)149U, (uint8_t)128U, (uint8_t)93U, (uint8_t)195U, (uint8_t)25U, (uint8_t)254U,
    (uint8_t)105U, (uint8_t)99U, (uint8_t)228U, (uint8_t)196U, (uint8_t)218U, (uint8_t)175U,
    (uint8_t)53U, (uint8_t)95U, (uint8_t)114U, (uint8_t)46U, (uint8_t)186U, (uint8_t)116U,
    (uint8_t)107U, (uint8_t)146U
  };

static uint8_t
vectors_low45[128U] =
  {
    (uint8_t)196U, (uint8_t)231U, (uint8_t)83U, (uint8_t)46U, (uint8_t)232U, (uint8_t)22U,
    (uint8_t)120U, (uint8_t)156U, (uint8_t)45U, (uint8_t)61U, (uint8_t)169U, (uint8_t)255U,
    (uint8_t)159U, (uint8_t)75U, (uint8_t)55U, (uint8_t)19U, (uint8_t)154U, (uint8_t)133U,
    (uint8_t)21U, (uint8_t)219U, (uint8_t)248U, (uint8_t)249U, (uint8_t)225U, (uint8_t)208U,
    (uint8_t)191U, (uint8_t)0U, (uint8_t)193U, (uint8_t)42U, (uint8_t)221U, (uint8_t)215U,
    (uint8_t)158U, (uint8_t)187U, (uint8_t)215U, (uint8_t)98U, (uint8_t)54U, (uint8_t)247U,
    (uint8_t)95U, (uint8_t)42U, (uint8_t)167U, (uint8_t)5U, (uint8_t)160U, (uint8_t)159U,
    (uint8_t)121U, (uint8_t)85U, (uint8_t)3U, (uint8_t)142U, (uint8_t)191U, (uint8_t)240U,
    (uint8_t)213U, (uint8_t)102U, (uint8_t)145U, (uint8_t)28U, (uint8_t)94U, (uint8_t)161U,
    (uint8_t)50U, (uint8_t)20U, (uint8_t)226U, (uint8_t)194U, (uint8_t)238U, (uint8_t)180U,
    (uint8_t)109U, (uint8_t)35U, (uint8_t)173U, (uint8_t)134U, (uint8_t)163U, (uint8_t)59U,
    (uint8_t)96U, (uint8_t)247U, (uint8_t)185U, (uint8_t)68U, (uint8_t)141U, (uint8_t)99U,
    (uint8_t)238U, (uint8_t)195U, (uint8_t)225U, (uint8_t)213U, (uint8_t)159U, (uint8_t)72U,
    (uint8_t)179U, (uint8_t)149U, (uint8_t)82U, (uint8_t)133U, (uint8_t)116U, (uint8_t)71U,
    (uint8_t)220U, (uint8_t)93U, (uint8_t)121U, (uint8_t)68U, (uint8_t)102U, (uint8_t)122U,
    (uint8_t)35U, (uint8_t)14U, (uint8_t)61U, (uint8_t)191U, (uint8_t)163U, (uint8_t)12U,
    (uint8_t)163U, (uint8_t)34U, (uint8_t)246U, (uint8_t)234U, (uint8_t)202U, (uint8_t)247U,
    (uint8_t)83U, (uint8_t)106U, (uint8_t)40U, (uint8_t)103U, (uint8_t)6U, (uint8_t)166U,
    (uint8_t)39U, (uint8_t)197U, (uint8_t)8U, (uint8_t)60U, (uint8_t)50U, (uint8_t)222U,
    (uint8_t)6U, (uint8_t)88U, (uint8_t)185U, (uint8_t)7U, (uint8_t)56U, (uint8_t)87U,
    (uint8_t)195U, (uint8_t)15U, (uint8_t)177U, (uint8_t)216U, (uint8_t)110U, (uint8_t)184U,
    (uint8_t)173U, (uint8_t)27U
  };

static uint8_t
vectors_low46[32U] =
  {
    (uint8_t)161U, (uint8_t)213U, (uint8_t)187U, (uint8_t)125U, (uint8_t)112U, (uint8_t)98U,
    (uint8_t)29U, (uint8_t)238U, (uint8_t)107U, (uint8_t)102U, (uint8_t)139U, (uint8_t)40U,
    (uint8_t)197U, (uint8_t)109U, (uint8_t)86U, (uint8_t)16U, (uint8_t)194U, (uint8_t)248U,
    (uint8_t)206U, (uint8_t)211U, (uint8_t)2U, (uint8_t)132U, (uint8_t)204U, (uint8_t)62U,
    (uint8_t)14U, (uint8_t)72U, (uint8_t)222U, (uint8_t)51U, (uint8_t)26U, (uint8_t)240U,
    (uint8_t)80U, (uint8_t)98U
  };

static uint8_t
vectors_low47[16U] =
  {
    (uint8_t)136U, (uint8_t)164U, (uint8_t)158U, (uint8_t)62U, (uint8_t)84U, (uint8_t)197U,
    (uint8_t)234U, (uint8_t)84U, (uint8_t)201U, (uint8_t)139U, (uint8_t)149U, (uint8_t)222U,
    (uint8_t)129U, (uint8_t)188U, (uint8_t)200U, (uint8_t)7U
  };

static uint8_t
vectors_low48[32U] =
  {
    (uint8_t)180U, (uint8_t)226U, (uint8_t)66U, (uint8_t)110U, (uint8_t)152U, (uint8_t)246U,
    (uint8_t)238U, (uint8_t)217U, (uint8_t)122U, (uint8_t)108U, (uint8_t)223U, (uint8_t)105U,
    (uint8_t)10U, (uint8_t)137U, (uint8_t)238U, (uint8_t)16U, (uint8_t)158U, (uint8_t)132U,
    (uint8_t)195U, (uint8_t)220U, (uint8_t)161U, (uint8_t)108U, (uint8_t)136U, (uint8_t)60U,
    (uint8_t)38U, (uint8_t)250U, (uint8_t)74U, (uint8_t)198U, (uint8_t)113U, (uint8_t)99U,
    (uint8_t)141U, (uint8_t)141U
  };

static uint8_t
vectors_low49[32U] =
  {
    (uint8_t)91U, (uint8_t)209U, (uint8_t)224U, (uint8_t)134U, (uint8_t)237U, (uint8_t)34U,
    (uint8_t)140U, (uint8_t)253U, (uint8_t)139U, (uint8_t)85U, (uint8_t)193U, (uint8_t)115U,
    (uint8_t)31U, (uint8_t)234U, (uint8_t)64U, (uint8_t)195U, (uint8_t)166U, (uint8_t)61U,
    (uint8_t)2U, (uint8_t)37U, (uint8_t)153U, (uint8_t)202U, (uint8_t)45U, (uint8_t)164U,
    (uint8_t)187U, (uint8_t)35U, (uint8_t)17U, (uint8_t)143U, (uint8_t)72U, (uint8_t)33U,
    (uint8_t)186U, (uint8_t)98U
  };

static uint8_t
vectors_low50[32U] =
  {
    (uint8_t)183U, (uint8_t)84U, (uint8_t)181U, (uint8_t)58U, (uint8_t)194U, (uint8_t)38U,
    (uint8_t)232U, (uint8_t)235U, (uint8_t)228U, (uint8_t)122U, (uint8_t)61U, (uint8_t)49U,
    (uint8_t)73U, (uint8_t)110U, (uint8_t)200U, (uint8_t)34U, (uint8_t)222U, (uint8_t)6U,
    (uint8_t)252U, (uint8_t)162U, (uint8_t)231U, (uint8_t)239U, (uint8_t)91U, (uint8_t)241U,
    (uint8_t)222U, (uint8_t)198U, (uint8_t)200U, (uint8_t)61U, (uint8_t)5U, (uint8_t)54U,
    (uint8_t)142U, (uint8_t)195U
  };

static uint8_t
vectors_low51[32U] =
  {
    (uint8_t)250U, (uint8_t)126U, (uint8_t)118U, (uint8_t)178U, (uint8_t)128U, (uint8_t)93U,
    (uint8_t)144U, (uint8_t)179U, (uint8_t)216U, (uint8_t)159U, (uint8_t)255U, (uint8_t)84U,
    (uint8_t)80U, (uint8_t)16U, (uint8_t)216U, (uint8_t)79U, (uint8_t)103U, (uint8_t)170U,
    (uint8_t)58U, (uint8_t)44U, (uint8_t)158U, (uint8_t)178U, (uint8_t)186U, (uint8_t)35U,
    (uint8_t)46U, (uint8_t)117U, (uint8_t)244U, (uint8_t)213U, (uint8_t)50U, (uint8_t)103U,
    (uint8_t)218U, (uint8_t)195U
  };

static uint8_t
vectors_low52[128U] =
  {
    (uint8_t)223U, (uint8_t)107U, (uint8_t)36U, (uint8_t)96U, (uint8_t)104U, (uint8_t)143U,
    (uint8_t)165U, (uint8_t)55U, (uint8_t)223U, (uint8_t)61U, (uint8_t)223U, (uint8_t)229U,
    (uint8_t)87U, (uint8_t)95U, (uint8_t)202U, (uint8_t)94U, (uint8_t)184U, (uint8_t)171U,
    (uint8_t)173U, (uint8_t)86U, (uint8_t)203U, (uint8_t)196U, (uint8_t)229U, (uint8_t)166U,
    (uint8_t)24U, (uint8_t)162U, (uint8_t)180U, (uint8_t)167U, (uint8_t)218U, (uint8_t)246U,
    (uint8_t)226U, (uint8_t)21U, (uint8_t)195U, (uint8_t)164U, (uint8_t)151U, (uint8_t)151U,
    (uint8_t)76U, (uint8_t)80U, (uint8_t)47U, (uint8_t)157U, (uint8_t)14U, (uint8_t)195U,
    (uint8_t)93U, (uint8_t)227U, (uint8_t)252U, (uint8_t)46U, (uint8_t)165U, (uint8_t)212U,
    (uint8_t)241U, (uint8_t)13U, (uint8_t)233U, (uint8_t)178U, (uint8_t)174U, (uint8_t)230U,
    (uint8_t)109U, (uint8_t)204U, (uint8_t)126U, (uint8_t)122U, (uint8_t)230U, (uint8_t)53U,
    (uint8_t)121U, (uint8_t)131U, (uint8_t)9U, (uint8_t)89U, (uint8_t)89U, (uint8_t)184U,
    (uint8_t)23U, (uint8_t)240U, (uint8_t)56U, (uint8_t)62U, (uint8_t)48U, (uint8_t)48U,
    (uint8_t)119U, (uint8_t)27U, (uint8_t)210U, (uint8_t)237U, (uint8_t)151U, (uint8_t)64U,
    (uint8_t)106U, (uint8_t)207U, (uint8_t)120U, (uint8_t)161U, (uint8_t)164U, (uint8_t)165U,
    (uint8_t)243U, (uint8_t)15U, (uint8_t)160U, (uint8_t)153U, (uint8_t)34U, (uint8_t)137U,
    (uint8_t)201U, (uint8_t)32U, (uint8_t)46U, (uint8_t)105U, (uint8_t)227U, (uint8_t)235U,
    (uint8_t)30U, (uint8_t)171U, (uint8_t)226U, (uint8_t)39U, (uint8_t)193U, (uint8_t)20U,
    (uint8_t)9U, (uint8_t)255U, (uint8_t)67U, (uint8_t)15U, (uint8_t)109U, (uint8_t)252U,
    (uint8_t)161U, (uint8_t)169U, (uint8_t)35U, (uint8_t)168U, (uint8_t)177U, (uint8_t)123U,
    (uint8_t)196U, (uint8_t)184U, (uint8_t)126U, (uint8_t)144U, (uint8_t)128U, (uint8_t)7U,
    (uint8_t)245U, (uint8_t)233U, (uint8_t)117U, (uint8_t)156U, (uint8_t)65U, (uint8_t)72U,
    (uint8_t)43U, (uint8_t)1U
  };

static uint8_t
vectors_low53[32U] =
  {
    (uint8_t)104U, (uint8_t)242U, (uint8_t)29U, (uint8_t)20U, (uint8_t)82U, (uint8_t)93U,
    (uint8_t)86U, (uint8_t)35U, (uint8_t)60U, (uint8_t)126U, (uint8_t)38U, (uint8_t)52U,
    (uint8_t)130U, (uint8_t)211U, (uint8_t)68U, (uint8_t)195U, (uint8_t)136U, (uint8_t)168U,
    (uint8_t)64U, (uint8_t)16U, (uint8_t)58U, (uint8_t)119U, (uint8_t)251U, (uint8_t)32U,
    (uint8_t)172U, (uint8_t)96U, (uint8_t)206U, (uint8_t)70U, (uint8_t)60U, (uint8_t)171U,
    (uint8_t)220U, (uint8_t)121U
  };

static uint8_t
vectors_low54[16U] =
  {
    (uint8_t)89U, (uint8_t)250U, (uint8_t)128U, (uint8_t)174U, (uint8_t)87U, (uint8_t)15U,
    (uint8_t)62U, (uint8_t)12U, (uint8_t)96U, (uint8_t)172U, (uint8_t)126U, (uint8_t)37U,
    (uint8_t)120U, (uint8_t)206U, (uint8_t)195U, (uint8_t)203U
  };

static uint8_t
vectors_low55[32U] =
  {
    (uint8_t)117U, (uint8_t)132U, (uint8_t)180U, (uint8_t)22U, (uint8_t)101U, (uint8_t)48U,
    (uint8_t)68U, (uint8_t)47U, (uint8_t)6U, (uint8_t)226U, (uint8_t)65U, (uint8_t)221U,
    (uint8_t)144U, (uint8_t)79U, (uint8_t)86U, (uint8_t)33U, (uint8_t)103U, (uint8_t)226U,
    (uint8_t)253U, (uint8_t)174U, (uint8_t)50U, (uint8_t)71U, (uint8_t)171U, (uint8_t)133U,
    (uint8_t)58U, (uint8_t)74U, (uint8_t)157U, (uint8_t)72U, (uint8_t)132U, (uint8_t)165U,
    (uint8_t)250U, (uint8_t)70U
  };

static uint8_t
vectors_low56[32U] =
  {
    (uint8_t)246U, (uint8_t)165U, (uint8_t)72U, (uint8_t)47U, (uint8_t)19U, (uint8_t)144U,
    (uint8_t)69U, (uint8_t)197U, (uint8_t)56U, (uint8_t)156U, (uint8_t)146U, (uint8_t)70U,
    (uint8_t)215U, (uint8_t)114U, (uint8_t)199U, (uint8_t)130U, (uint8_t)196U, (uint8_t)235U,
    (uint8_t)247U, (uint8_t)156U, (uint8_t)58U, (uint8_t)132U, (uint8_t)181U, (uint8_t)207U,
    (uint8_t)119U, (uint8_t)159U, (uint8_t)69U, (uint8_t)138U, (uint8_t)105U, (uint8_t)165U,
    (uint8_t)41U, (uint8_t)20U
  };

static uint8_t
vectors_low57[32U] =
  {
    (uint8_t)157U, (uint8_t)55U, (uint8_t)177U, (uint8_t)206U, (uint8_t)153U, (uint8_t)248U,
    (uint8_t)7U, (uint8_t)153U, (uint8_t)147U, (uint8_t)221U, (uint8_t)240U, (uint8_t)189U,
    (uint8_t)84U, (uint8_t)186U, (uint8_t)178U, (uint8_t)24U, (uint8_t)1U, (uint8_t)102U,
    (uint8_t)133U, (uint8_t)178U, (uint8_t)38U, (uint8_t)85U, (uint8_t)166U, (uint8_t)120U,
    (uint8_t)206U, (uint8_t)67U, (uint8_t)0U, (uint8_t)16U, (uint8_t)95U, (uint8_t)58U,
    (uint8_t)69U, (uint8_t)183U
  };

static uint8_t
vectors_low58[32U] =
  {
    (uint8_t)76U, (uint8_t)151U, (uint8_t)198U, (uint8_t)112U, (uint8_t)38U, (uint8_t)255U,
    (uint8_t)67U, (uint8_t)194U, (uint8_t)238U, (uint8_t)115U, (uint8_t)14U, (uint8_t)123U,
    (uint8_t)44U, (uint8_t)232U, (uint8_t)204U, (uint8_t)228U, (uint8_t)121U, (uint8_t)79U,
    (uint8_t)208U, (uint8_t)88U, (uint8_t)141U, (uint8_t)235U, (uint8_t)22U, (uint8_t)24U,
    (uint8_t)95U, (uint8_t)166U, (uint8_t)121U, (uint8_t)45U, (uint8_t)221U, (uint8_t)13U,
    (uint8_t)70U, (uint8_t)222U
  };

static uint8_t
vectors_low59[128U] =
  {
    (uint8_t)229U, (uint8_t)248U, (uint8_t)135U, (uint8_t)75U, (uint8_t)224U, (uint8_t)168U,
    (uint8_t)52U, (uint8_t)90U, (uint8_t)171U, (uint8_t)242U, (uint8_t)248U, (uint8_t)41U,
    (uint8_t)167U, (uint8_t)192U, (uint8_t)107U, (uint8_t)180U, (uint8_t)14U, (uint8_t)96U,
    (uint8_t)134U, (uint8_t)149U, (uint8_t)8U, (uint8_t)194U, (uint8_t)189U, (uint8_t)239U,
    (uint8_t)7U, (uint8_t)29U, (uint8_t)115U, (uint8_t)105U, (uint8_t)44U, (uint8_t)2U,
    (uint8_t)101U, (uint8_t)246U, (uint8_t)165U, (uint8_t)191U, (uint8_t)156U, (uint8_t)166U,
    (uint8_t)207U, (uint8_t)71U, (uint8_t)215U, (uint8_t)92U, (uint8_t)189U, (uint8_t)157U,
    (uint8_t)248U, (uint8_t)139U, (uint8_t)156U, (uint8_t)178U, (uint8_t)54U, (uint8_t)205U,
    (uint8_t)252U, (uint8_t)227U, (uint8_t)125U, (uint8_t)47U, (uint8_t)212U, (uint8_t)145U,
    (uint8_t)63U, (uint8_t)23U, (uint8_t)125U, (uint8_t)189U, (uint8_t)65U, (uint8_t)136U,
    (uint8_t)125U, (uint8_t)174U, (uint8_t)17U, (uint8_t)110U, (uint8_t)223U, (uint8_t)189U,
    (uint8_t)173U, (uint8_t)79U, (uint8_t)214U, (uint8_t)228U, (uint8_t)193U, (uint8_t)165U,
    (uint8_t)26U, (uint8_t)173U, (uint8_t)159U, (uint8_t)157U, (uint8_t)106U, (uint8_t)254U,
    (uint8_t)127U, (uint8_t)202U, (uint8_t)252U, (uint8_t)237U, (uint8_t)69U, (uint8_t)164U,
    (uint8_t)145U, (uint8_t)61U, (uint8_t)116U, (uint8_t)42U, (uint8_t)126U, (uint8_t)192U,
    (uint8_t)15U, (uint8_t)214U, (uint8_t)23U, (uint8_t)13U, (uint8_t)99U, (uint8_t)166U,
    (uint8_t)143U, (uint8_t)152U, (uint8_t)109U, (uint8_t)140U, (uint8_t)35U, (uint8_t)87U,
    (uint8_t)118U, (uint8_t)94U, (uint8_t)77U, (uint8_t)56U, (uint8_t)131U, (uint8_t)93U,
    (uint8_t)63U, (uint8_t)234U, (uint8_t)48U, (uint8_t)26U, (uint8_t)250U, (uint8_t)180U,
    (uint8_t)58U, (uint8_t)80U, (uint8_t)189U, (uint8_t)158U, (uint8_t)221U, (uint8_t)45U,
    (uint8_t)236U, (uint8_t)106U, (uint8_t)151U, (uint8_t)151U, (uint8_t)50U, (uint8_t)178U,
    (uint8_t)82U, (uint8_t)146U
  };

static uint8_t
vectors_low60[32U] =
  {
    (uint8_t)26U, (uint8_t)225U, (uint8_t)42U, (uint8_t)94U, (uint8_t)78U, (uint8_t)154U,
    (uint8_t)74U, (uint8_t)91U, (uint8_t)250U, (uint8_t)121U, (uint8_t)218U, (uint8_t)48U,
    (uint8_t)169U, (uint8_t)230U, (uint8_t)198U, (uint8_t)47U, (uint8_t)252U, (uint8_t)99U,
    (uint8_t)149U, (uint8_t)114U, (uint8_t)239U, (uint8_t)18U, (uint8_t)84U, (uint8_t)25U,
    (uint8_t)77U, (uint8_t)18U, (uint8_t)154U, (uint8_t)22U, (uint8_t)235U, (uint8_t)83U,
    (uint8_t)199U, (uint8_t)22U
  };

static uint8_t
vectors_low61[16U] =
  {
    (uint8_t)83U, (uint8_t)153U, (uint8_t)179U, (uint8_t)72U, (uint8_t)31U, (uint8_t)223U,
    (uint8_t)36U, (uint8_t)211U, (uint8_t)115U, (uint8_t)34U, (uint8_t)34U, (uint8_t)103U,
    (uint8_t)121U, (uint8_t)10U, (uint8_t)15U, (uint8_t)236U
  };

static uint8_t
vectors_low62[32U] =
  {
    (uint8_t)130U, (uint8_t)128U, (uint8_t)207U, (uint8_t)220U, (uint8_t)215U, (uint8_t)165U,
    (uint8_t)117U, (uint8_t)129U, (uint8_t)110U, (uint8_t)1U, (uint8_t)153U, (uint8_t)225U,
    (uint8_t)21U, (uint8_t)218U, (uint8_t)14U, (uint8_t)167U, (uint8_t)124U, (uint8_t)174U,
    (uint8_t)157U, (uint8_t)48U, (uint8_t)180U, (uint8_t)156U, (uint8_t)137U, (uint8_t)26U,
    (uint8_t)108U, (uint8_t)34U, (uint8_t)94U, (uint8_t)144U, (uint8_t)55U, (uint8_t)186U,
    (uint8_t)103U, (uint8_t)226U
  };

static uint8_t
vectors_low63[32U] =
  {
    (uint8_t)104U, (uint8_t)21U, (uint8_t)84U, (uint8_t)255U, (uint8_t)112U, (uint8_t)38U,
    (uint8_t)88U, (uint8_t)18U, (uint8_t)46U, (uint8_t)145U, (uint8_t)186U, (uint8_t)1U,
    (uint8_t)116U, (uint8_t)80U, (uint8_t)207U, (uint8_t)223U, (uint8_t)200U, (uint8_t)227U,
    (uint8_t)244U, (uint8_t)145U, (uint8_t)17U, (uint8_t)83U, (uint8_t)247U, (uint8_t)188U,
    (uint8_t)196U, (uint8_t)40U, (uint8_t)64U, (uint8_t)62U, (uint8_t)156U, (uint8_t)123U,
    (uint8_t)157U, (uint8_t)104U
  };

static uint8_t
vectors_low64[32U] =
  {
    (uint8_t)34U, (uint8_t)103U, (uint8_t)50U, (uint8_t)183U, (uint8_t)164U, (uint8_t)87U,
    (uint8_t)207U, (uint8_t)10U, (uint8_t)192U, (uint8_t)239U, (uint8_t)9U, (uint8_t)253U,
    (uint8_t)79U, (uint8_t)129U, (uint8_t)41U, (uint8_t)101U, (uint8_t)115U, (uint8_t)180U,
    (uint8_t)154U, (uint8_t)104U, (uint8_t)222U, (uint8_t)94U, (uint8_t)122U, (uint8_t)195U,
    (uint8_t)7U, (uint8_t)14U, (uint8_t)20U, (uint8_t)140U, (uint8_t)149U, (uint8_t)232U,
    (uint8_t)227U, (uint8_t)35U
  };

static uint8_t
vectors_low65[32U] =
  {
    (uint8_t)69U, (uint8_t)148U, (uint8_t)43U, (uint8_t)94U, (uint8_t)154U, (uint8_t)26U,
    (uint8_t)18U, (uint8_t)142U, (uint8_t)133U, (uint8_t)225U, (uint8_t)44U, (uint8_t)52U,
    (uint8_t)89U, (uint8_t)99U, (uint8_t)116U, (uint8_t)221U, (uint8_t)200U, (uint8_t)95U,
    (uint8_t)215U, (uint8_t)80U, (uint8_t)46U, (uint8_t)86U, (uint8_t)51U, (uint8_t)199U,
    (uint8_t)57U, (uint8_t)15U, (uint8_t)198U, (uint8_t)230U, (uint8_t)241U, (uint8_t)229U,
    (uint8_t)239U, (uint8_t)86U
  };

static uint8_t
vectors_low66[32U] =
  {
    (uint8_t)111U, (uint8_t)197U, (uint8_t)153U, (uint8_t)41U, (uint8_t)180U, (uint8_t)30U,
    (uint8_t)119U, (uint8_t)7U, (uint8_t)40U, (uint8_t)134U, (uint8_t)175U, (uint8_t)244U,
    (uint8_t)95U, (uint8_t)115U, (uint8_t)123U, (uint8_t)68U, (uint8_t)155U, (uint8_t)16U,
    (uint8_t)94U, (uint8_t)215U, (uint8_t)234U, (uint8_t)203U, (uint8_t)215U, (uint8_t)76U,
    (uint8_t)124U, (uint8_t)191U, (uint8_t)237U, (uint8_t)245U, (uint8_t)51U, (uint8_t)219U,
    (uint8_t)234U, (uint8_t)161U
  };

static uint8_t
vectors_low67[128U] =
  {
    (uint8_t)183U, (uint8_t)84U, (uint8_t)115U, (uint8_t)50U, (uint8_t)225U, (uint8_t)80U,
    (uint8_t)150U, (uint8_t)99U, (uint8_t)252U, (uint8_t)254U, (uint8_t)162U, (uint8_t)18U,
    (uint8_t)143U, (uint8_t)127U, (uint8_t)58U, (uint8_t)61U, (uint8_t)244U, (uint8_t)132U,
    (uint8_t)205U, (uint8_t)141U, (uint8_t)240U, (uint8_t)52U, (uint8_t)176U, (uint8_t)1U,
    (uint8_t)153U, (uint8_t)21U, (uint8_t)125U, (uint8_t)53U, (uint8_t)214U, (uint8_t)30U,
    (uint8_t)53U, (uint8_t)241U, (uint8_t)169U, (uint8_t)212U, (uint8_t)129U, (uint8_t)199U,
    (uint8_t)210U, (uint8_t)232U, (uint8_t)19U, (uint8_t)5U, (uint8_t)97U, (uint8_t)109U,
    (uint8_t)112U, (uint8_t)252U, (uint8_t)55U, (uint8_t)30U, (uint8_t)228U, (uint8_t)89U,
    (uint8_t)176U, (uint8_t)178U, (uint8_t)38U, (uint8_t)125U, (uint8_t)98U, (uint8_t)126U,
    (uint8_t)146U, (uint8_t)133U, (uint8_t)144U, (uint8_t)237U, (uint8_t)202U, (uint8_t)195U,
    (uint8_t)35U, (uint8_t)24U, (uint8_t)152U, (uint8_t)178U, (uint8_t)78U, (uint8_t)243U,
    (uint8_t)120U, (uint8_t)170U, (uint8_t)156U, (uint8_t)61U, (uint8_t)56U, (uint8_t)22U,
    (uint8_t)25U, (uint8_t)246U, (uint8_t)101U, (uint8_t)55U, (uint8_t)155U, (uint8_t)231U,
    (uint8_t)108U, (uint8_t)124U, (uint8_t)27U, (uint8_t)213U, (uint8_t)53U, (uint8_t)80U,
    (uint8_t)92U, (uint8_t)86U, (uint8_t)61U, (uint8_t)179U, (uint8_t)114U, (uint8_t)95U,
    (uint8_t)3U, (uint8_t)71U, (uint8_t)134U, (uint8_t)227U, (uint8_t)91U, (uint8_t)221U,
    (uint8_t)144U, (uint8_t)66U, (uint8_t)147U, (uint8_t)5U, (uint8_t)253U, (uint8_t)113U,
    (uint8_t)215U, (uint8_t)191U, (uint8_t)104U, (uint8_t)14U, (uint8_t)140U, (uint8_t)221U,
    (uint8_t)109U, (uint8_t)76U, (uint8_t)52U, (uint8_t)141U, (uint8_t)151U, (uint8_t)7U,
    (uint8_t)143U, (uint8_t)92U, (uint8_t)245U, (uint8_t)232U, (uint8_t)157U, (uint8_t)238U,
    (uint8_t)45U, (uint8_t)196U, (uint8_t)16U, (uint8_t)250U, (uint8_t)212U, (uint8_t)242U,
    (uint8_t)163U, (uint8_t)15U
  };

static uint8_t
vectors_low68[32U] =
  {
    (uint8_t)16U, (uint8_t)184U, (uint8_t)120U, (uint8_t)156U, (uint8_t)219U, (uint8_t)214U,
    (uint8_t)119U, (uint8_t)132U, (uint8_t)66U, (uint8_t)164U, (uint8_t)94U, (uint8_t)223U,
    (uint8_t)34U, (uint8_t)139U, (uint8_t)153U, (uint8_t)35U, (uint8_t)244U, (uint8_t)82U,
    (uint8_t)99U, (uint8_t)26U, (uint8_t)208U, (uint8_t)254U, (uint8_t)158U, (uint8_t)96U,
    (uint8_t)141U, (uint8_t)16U, (uint8_t)130U, (uint8_t)107U, (uint8_t)167U, (uint8_t)29U,
    (uint8_t)167U, (uint8_t)202U
  };

static uint8_t
vectors_low69[16U] =
  {
    (uint8_t)21U, (uint8_t)159U, (uint8_t)197U, (uint8_t)216U, (uint8_t)229U, (uint8_t)14U,
    (uint8_t)181U, (uint8_t)110U, (uint8_t)34U, (uint8_t)151U, (uint8_t)71U, (uint8_t)137U,
    (uint8_t)177U, (uint8_t)220U, (uint8_t)32U, (uint8_t)209U
  };

static uint8_t
vectors_low70[32U] =
  {
    (uint8_t)45U, (uint8_t)213U, (uint8_t)158U, (uint8_t)55U, (uint8_t)118U, (uint8_t)108U,
    (uint8_t)102U, (uint8_t)117U, (uint8_t)113U, (uint8_t)183U, (uint8_t)121U, (uint8_t)192U,
    (uint8_t)110U, (uint8_t)18U, (uint8_t)186U, (uint8_t)33U, (uint8_t)145U, (uint8_t)136U,
    (uint8_t)72U, (uint8_t)151U, (uint8_t)114U, (uint8_t)244U, (uint8_t)134U, (uint8_t)49U,
    (uint8_t)166U, (uint8_t)114U, (uint8_t)139U, (uint8_t)91U, (uint8_t)134U, (uint8_t)126U,
    (uint8_t)60U, (uint8_t)244U
  };

static uint8_t
vectors_low71[32U] =
  {
    (uint8_t)150U, (uint8_t)109U, (uint8_t)148U, (uint8_t)32U, (uint8_t)56U, (uint8_t)3U,
    (uint8_t)5U, (uint8_t)9U, (uint8_t)178U, (uint8_t)14U, (uint8_t)97U, (uint8_t)0U, (uint8_t)98U,
    (uint8_t)4U, (uint8_t)43U, (uint8_t)107U, (uint8_t)241U, (uint8_t)4U, (uint8_t)129U,
    (uint8_t)40U, (uint8_t)24U, (uint8_t)137U, (uint8_t)50U, (uint8_t)146U, (uint8_t)166U,
    (uint8_t)141U, (uint8_t)87U, (uint8_t)209U, (uint8_t)206U, (uint8_t)134U, (uint8_t)81U,
    (uint8_t)81U
  };

static uint8_t
vectors_low72[128U] =
  {
    (uint8_t)62U, (uint8_t)106U, (uint8_t)205U, (uint8_t)139U, (uint8_t)78U, (uint8_t)133U,
    (uint8_t)180U, (uint8_t)160U, (uint8_t)247U, (uint8_t)146U, (uint8_t)143U, (uint8_t)107U,
    (uint8_t)212U, (uint8_t)26U, (uint8_t)142U, (uint8_t)107U, (uint8_t)82U, (uint8_t)82U,
    (uint8_t)79U, (uint8_t)231U, (uint8_t)39U, (uint8_t)35U, (uint8_t)160U, (uint8_t)80U,
    (uint8_t)150U, (uint8_t)55U, (uint8_t)211U, (uint8_t)63U, (uint8_t)21U, (uint8_t)175U,
    (uint8_t)231U, (uint8_t)216U, (uint8_t)218U, (uint8_t)106U, (uint8_t)21U, (uint8_t)32U,
    (uint8_t)155U, (uint8_t)158U, (uint8_t)65U, (uint8_t)73U, (uint8_t)87U, (uint8_t)111U,
    (uint8_t)187U, (uint8_t)31U, (uint8_t)216U, (uint8_t)49U, (uint8_t)247U, (uint8_t)132U,
    (uint8_t)192U, (uint8_t)68U, (uint8_t)57U, (uint8_t)171U, (uint8_t)218U, (uint8_t)70U,
    (uint8_t)5U, (uint8_t)208U, (uint8_t)101U, (uint8_t)86U, (uint8_t)220U, (uint8_t)48U,
    (uint8_t)2U, (uint8_t)5U, (uint8_t)91U, (uint8_t)88U, (uint8_t)85U, (uint8_t)251U,
    (uint8_t)162U, (uint8_t)1U, (uint8_t)246U, (uint8_t)218U, (uint8_t)239U, (uint8_t)121U,
    (uint8_t)247U, (uint8_t)141U, (uint8_t)0U, (uint8_t)30U, (uint8_t)214U, (uint8_t)158U,
    (uint8_t)202U, (uint8_t)138U, (uint8_t)65U, (uint8_t)133U, (uint8_t)19U, (uint8_t)208U,
    (uint8_t)36U, (uint8_t)100U, (uint8_t)232U, (uint8_t)215U, (uint8_t)66U, (uint8_t)194U,
    (uint8_t)121U, (uint8_t)156U, (uint8_t)214U, (uint8_t)142U, (uint8_t)223U, (uint8_t)190U,
    (uint8_t)136U, (uint8_t)174U, (uint8_t)155U, (uint8_t)53U, (uint8_t)160U, (uint8_t)170U,
    (uint8_t)6U, (uint8_t)92U, (uint8_t)66U, (uint8_t)164U, (uint8_t)119U, (uint8_t)0U,
    (uint8_t)88U, (uint8_t)196U, (uint8_t)176U, (uint8_t)38U, (uint8_t)208U, (uint8_t)53U,
    (uint8_t)10U, (uint8_t)122U, (uint8_t)250U, (uint8_t)156U, (uint8_t)82U, (uint8_t)195U,
    (uint8_t)199U, (uint8_t)250U, (uint8_t)5U, (uint8_t)79U, (uint8_t)138U, (uint8_t)150U,
    (uint8_t)216U, (uint8_t)135U
  };

static uint8_t
vectors_low73[32U] =
  {
    (uint8_t)229U, (uint8_t)250U, (uint8_t)115U, (uint8_t)190U, (uint8_t)217U, (uint8_t)147U,
    (uint8_t)64U, (uint8_t)201U, (uint8_t)26U, (uint8_t)177U, (uint8_t)125U, (uint8_t)3U,
    (uint8_t)158U, (uint8_t)253U, (uint8_t)36U, (uint8_t)143U, (uint8_t)205U, (uint8_t)26U,
    (uint8_t)184U, (uint8_t)176U, (uint8_t)160U, (uint8_t)246U, (uint8_t)85U, (uint8_t)221U,
    (uint8_t)49U, (uint8_t)73U, (uint8_t)148U, (uint8_t)150U, (uint8_t)133U, (uint8_t)236U,
    (uint8_t)173U, (uint8_t)189U
  };

static uint8_t
vectors_low74[16U] =
  {
    (uint8_t)175U, (uint8_t)75U, (uint8_t)148U, (uint8_t)240U, (uint8_t)131U, (uint8_t)0U,
    (uint8_t)161U, (uint8_t)235U, (uint8_t)5U, (uint8_t)154U, (uint8_t)214U, (uint8_t)166U,
    (uint8_t)135U, (uint8_t)162U, (uint8_t)47U, (uint8_t)209U
  };

static uint8_t
vectors_low75[32U] =
  {
    (uint8_t)208U, (uint8_t)9U, (uint8_t)90U, (uint8_t)79U, (uint8_t)215U, (uint8_t)246U,
    (uint8_t)214U, (uint8_t)222U, (uint8_t)42U, (uint8_t)31U, (uint8_t)11U, (uint8_t)41U,
    (uint8_t)44U, (uint8_t)71U, (uint8_t)236U, (uint8_t)232U, (uint8_t)86U, (uint8_t)91U,
    (uint8_t)248U, (uint8_t)194U, (uint8_t)2U, (uint8_t)240U, (uint8_t)114U, (uint8_t)61U,
    (uint8_t)13U, (uint8_t)231U, (uint8_t)242U, (uint8_t)247U, (uint8_t)144U, (uint8_t)69U,
    (uint8_t)55U, (uint8_t)191U
  };

static uint8_t
vectors_low76[32U] =
  {
    (uint8_t)77U, (uint8_t)216U, (uint8_t)31U, (uint8_t)173U, (uint8_t)83U, (uint8_t)74U,
    (uint8_t)163U, (uint8_t)110U, (uint8_t)23U, (uint8_t)77U, (uint8_t)6U, (uint8_t)102U,
    (uint8_t)110U, (uint8_t)149U, (uint8_t)164U, (uint8_t)217U, (uint8_t)179U, (uint8_t)98U,
    (uint8_t)43U, (uint8_t)246U, (uint8_t)13U, (uint8_t)138U, (uint8_t)86U, (uint8_t)44U,
    (uint8_t)118U, (uint8_t)69U, (uint8_t)65U, (uint8_t)234U, (uint8_t)124U, (uint8_t)151U,
    (uint8_t)79U, (uint8_t)233U
  };

static uint8_t
vectors_low77[32U] =
  {
    (uint8_t)17U, (uint8_t)124U, (uint8_t)160U, (uint8_t)170U, (uint8_t)157U, (uint8_t)87U,
    (uint8_t)151U, (uint8_t)48U, (uint8_t)5U, (uint8_t)250U, (uint8_t)209U, (uint8_t)248U,
    (uint8_t)160U, (uint8_t)47U, (uint8_t)45U, (uint8_t)98U, (uint8_t)172U, (uint8_t)112U,
    (uint8_t)23U, (uint8_t)88U, (uint8_t)85U, (uint8_t)107U, (uint8_t)66U, (uint8_t)168U,
    (uint8_t)213U, (uint8_t)56U, (uint8_t)46U, (uint8_t)229U, (uint8_t)85U, (uint8_t)64U,
    (uint8_t)168U, (uint8_t)107U
  };

static uint8_t
vectors_low78[32U] =
  {
    (uint8_t)163U, (uint8_t)107U, (uint8_t)164U, (uint8_t)30U, (uint8_t)9U, (uint8_t)90U,
    (uint8_t)64U, (uint8_t)243U, (uint8_t)121U, (uint8_t)133U, (uint8_t)165U, (uint8_t)205U,
    (uint8_t)115U, (uint8_t)21U, (uint8_t)243U, (uint8_t)119U, (uint8_t)49U, (uint8_t)50U,
    (uint8_t)244U, (uint8_t)145U, (uint8_t)239U, (uint8_t)138U, (uint8_t)69U, (uint8_t)61U,
    (uint8_t)57U, (uint8_t)112U, (uint8_t)174U, (uint8_t)114U, (uint8_t)244U, (uint8_t)28U,
    (uint8_t)83U, (uint8_t)101U
  };

static uint8_t
vectors_low79[32U] =
  {
    (uint8_t)171U, (uint8_t)186U, (uint8_t)29U, (uint8_t)22U, (uint8_t)37U, (uint8_t)86U,
    (uint8_t)234U, (uint8_t)171U, (uint8_t)114U, (uint8_t)146U, (uint8_t)82U, (uint8_t)205U,
    (uint8_t)72U, (uint8_t)222U, (uint8_t)173U, (uint8_t)45U, (uint8_t)125U, (uint8_t)80U,
    (uint8_t)166U, (uint8_t)56U, (uint8_t)91U, (uint8_t)29U, (uint8_t)39U, (uint8_t)5U,
    (uint8_t)145U, (uint8_t)212U, (uint8_t)101U, (uint8_t)250U, (uint8_t)56U, (uint8_t)197U,
    (uint8_t)89U, (uint8_t)125U
  };

static uint8_t
vectors_low80[128U] =
  {
    (uint8_t)43U, (uint8_t)239U, (uint8_t)1U, (uint8_t)190U, (uint8_t)161U, (uint8_t)251U,
    (uint8_t)10U, (uint8_t)181U, (uint8_t)252U, (uint8_t)203U, (uint8_t)180U, (uint8_t)116U,
    (uint8_t)161U, (uint8_t)186U, (uint8_t)203U, (uint8_t)54U, (uint8_t)31U, (uint8_t)252U,
    (uint8_t)195U, (uint8_t)38U, (uint8_t)241U, (uint8_t)217U, (uint8_t)241U, (uint8_t)150U,
    (uint8_t)144U, (uint8_t)72U, (uint8_t)195U, (uint8_t)146U, (uint8_t)242U, (uint8_t)118U,
    (uint8_t)30U, (uint8_t)208U, (uint8_t)163U, (uint8_t)113U, (uint8_t)38U, (uint8_t)67U,
    (uint8_t)51U, (uint8_t)17U, (uint8_t)222U, (uint8_t)201U, (uint8_t)219U, (uint8_t)24U,
    (uint8_t)89U, (uint8_t)100U, (uint8_t)72U, (uint8_t)203U, (uint8_t)129U, (uint8_t)78U,
    (uint8_t)218U, (uint8_t)21U, (uint8_t)27U, (uint8_t)38U, (uint8_t)78U, (uint8_t)60U,
    (uint8_t)164U, (uint8_t)100U, (uint8_t)178U, (uint8_t)93U, (uint8_t)228U, (uint8_t)1U,
    (uint8_t)176U, (uint8_t)227U, (uint8_t)139U, (uint8_t)67U, (uint8_t)233U, (uint8_t)60U,
    (uint8_t)100U, (uint8_t)246U, (uint8_t)117U, (uint8_t)243U, (uint8_t)122U, (uint8_t)217U,
    (uint8_t)30U, (uint8_t)149U, (uint8_t)194U, (uint8_t)78U, (uint8_t)105U, (uint8_t)151U,
    (uint8_t)220U, (uint8_t)64U, (uint8_t)50U, (uint8_t)250U, (uint8_t)98U, (uint8_t)186U,
    (uint8_t)0U, (uint8_t)243U, (uint8_t)200U, (uint8_t)167U, (uint8_t)146U, (uint8_t)214U,
    (uint8_t)181U, (uint8_t)57U, (uint8_t)164U, (uint8_t)232U, (uint8_t)41U, (uint8_t)11U,
    (uint8_t)16U, (uint8_t)23U, (uint8_t)59U, (uint8_t)107U, (uint8_t)53U, (uint8_t)247U,
    (uint8_t)39U, (uint8_t)143U, (uint8_t)52U, (uint8_t)244U, (uint8_t)13U, (uint8_t)247U,
    (uint8_t)196U, (uint8_t)207U, (uint8_t)38U, (uint8_t)81U, (uint8_t)131U, (uint8_t)80U,
    (uint8_t)223U, (uint8_t)167U, (uint8_t)226U, (uint8_t)67U, (uint8_t)98U, (uint8_t)50U,
    (uint8_t)12U, (uint8_t)132U, (uint8_t)70U, (uint8_t)150U, (uint8_t)58U, (uint8_t)154U,
    (uint8_t)19U, (uint8_t)105U
  };

static uint8_t
vectors_low81[32U] =
  {
    (uint8_t)12U, (uint8_t)44U, (uint8_t)36U, (uint8_t)40U, (uint8_t)127U, (uint8_t)38U,
    (uint8_t)76U, (uint8_t)29U, (uint8_t)83U, (uint8_t)41U, (uint8_t)209U, (uint8_t)137U,
    (uint8_t)137U, (uint8_t)231U, (uint8_t)249U, (uint8_t)206U, (uint8_t)6U, (uint8_t)184U,
    (uint8_t)169U, (uint8_t)68U, (uint8_t)109U, (uint8_t)38U, (uint8_t)205U, (uint8_t)144U,
    (uint8_t)237U, (uint8_t)113U, (uint8_t)135U, (uint8_t)146U, (uint8_t)177U, (uint8_t)61U,
    (uint8_t)173U, (uint8_t)148U
  };

static uint8_t
vectors_low82[16U] =
  {
    (uint8_t)253U, (uint8_t)1U, (uint8_t)208U, (uint8_t)56U, (uint8_t)56U, (uint8_t)107U,
    (uint8_t)55U, (uint8_t)112U, (uint8_t)159U, (uint8_t)141U, (uint8_t)160U, (uint8_t)53U,
    (uint8_t)121U, (uint8_t)248U, (uint8_t)43U, (uint8_t)204U
  };

static uint8_t
vectors_low83[32U] =
  {
    (uint8_t)5U, (uint8_t)181U, (uint8_t)35U, (uint8_t)204U, (uint8_t)248U, (uint8_t)128U,
    (uint8_t)191U, (uint8_t)176U, (uint8_t)218U, (uint8_t)131U, (uint8_t)160U, (uint8_t)94U,
    (uint8_t)78U, (uint8_t)178U, (uint8_t)234U, (uint8_t)40U, (uint8_t)204U, (uint8_t)117U,
    (uint8_t)161U, (uint8_t)228U, (uint8_t)249U, (uint8_t)224U, (uint8_t)156U, (uint8_t)138U,
    (uint8_t)57U, (uint8_t)89U, (uint8_t)177U, (uint8_t)134U, (uint8_t)34U, (uint8_t)69U,
    (uint8_t)59U, (uint8_t)220U
  };

static uint8_t
vectors_low84[32U] =
  {
    (uint8_t)133U, (uint8_t)224U, (uint8_t)106U, (uint8_t)140U, (uint8_t)163U, (uint8_t)167U,
    (uint8_t)65U, (uint8_t)130U, (uint8_t)28U, (uint8_t)58U, (uint8_t)42U, (uint8_t)136U,
    (uint8_t)24U, (uint8_t)19U, (uint8_t)22U, (uint8_t)117U, (uint8_t)19U, (uint8_t)110U,
    (uint8_t)253U, (uint8_t)88U, (uint8_t)65U, (uint8_t)203U, (uint8_t)150U, (uint8_t)231U,
    (uint8_t)221U, (uint8_t)236U, (uint8_t)121U, (uint8_t)67U, (uint8_t)204U, (uint8_t)22U,
    (uint8_t)159U, (uint8_t)163U
  };

static uint8_t
vectors_low85[32U] =
  {
    (uint8_t)107U, (uint8_t)132U, (uint8_t)46U, (uint8_t)28U, (uint8_t)253U, (uint8_t)204U,
    (uint8_t)98U, (uint8_t)3U, (uint8_t)250U, (uint8_t)55U, (uint8_t)80U, (uint8_t)207U,
    (uint8_t)179U, (uint8_t)199U, (uint8_t)34U, (uint8_t)247U, (uint8_t)168U, (uint8_t)80U,
    (uint8_t)20U, (uint8_t)192U, (uint8_t)110U, (uint8_t)120U, (uint8_t)218U, (uint8_t)142U,
    (uint8_t)166U, (uint8_t)31U, (uint8_t)15U, (uint8_t)158U, (uint8_t)124U, (uint8_t)32U,
    (uint8_t)203U, (uint8_t)74U
  };

static uint8_t
vectors_low86[32U] =
  {
    (uint8_t)123U, (uint8_t)164U, (uint8_t)161U, (uint8_t)73U, (uint8_t)74U, (uint8_t)11U,
    (uint8_t)73U, (uint8_t)131U, (uint8_t)136U, (uint8_t)249U, (uint8_t)77U, (uint8_t)23U,
    (uint8_t)38U, (uint8_t)184U, (uint8_t)186U, (uint8_t)246U, (uint8_t)62U, (uint8_t)68U,
    (uint8_t)160U, (uint8_t)60U, (uint8_t)43U, (uint8_t)251U, (uint8_t)191U, (uint8_t)243U,
    (uint8_t)90U, (uint8_t)208U, (uint8_t)57U, (uint8_t)179U, (uint8_t)152U, (uint8_t)129U,
    (uint8_t)114U, (uint8_t)10U
  };

static uint8_t
vectors_low87[128U] =
  {
    (uint8_t)177U, (uint8_t)0U, (uint8_t)30U, (uint8_t)120U, (uint8_t)253U, (uint8_t)178U,
    (uint8_t)109U, (uint8_t)201U, (uint8_t)46U, (uint8_t)35U, (uint8_t)137U, (uint8_t)236U,
    (uint8_t)14U, (uint8_t)181U, (uint8_t)235U, (uint8_t)48U, (uint8_t)89U, (uint8_t)244U,
    (uint8_t)74U, (uint8_t)180U, (uint8_t)242U, (uint8_t)234U, (uint8_t)214U, (uint8_t)199U,
    (uint8_t)74U, (uint8_t)118U, (uint8_t)21U, (uint8_t)171U, (uint8_t)134U, (uint8_t)135U,
    (uint8_t)56U, (uint8_t)24U, (uint8_t)152U, (uint8_t)245U, (uint8_t)176U, (uint8_t)216U,
    (uint8_t)56U, (uint8_t)36U, (uint8_t)127U, (uint8_t)65U, (uint8_t)120U, (uint8_t)107U,
    (uint8_t)184U, (uint8_t)60U, (uint8_t)7U, (uint8_t)119U, (uint8_t)19U, (uint8_t)255U,
    (uint8_t)132U, (uint8_t)84U, (uint8_t)14U, (uint8_t)213U, (uint8_t)64U, (uint8_t)97U,
    (uint8_t)244U, (uint8_t)208U, (uint8_t)2U, (uint8_t)100U, (uint8_t)105U, (uint8_t)157U,
    (uint8_t)244U, (uint8_t)118U, (uint8_t)135U, (uint8_t)60U, (uint8_t)13U, (uint8_t)208U,
    (uint8_t)195U, (uint8_t)99U, (uint8_t)185U, (uint8_t)152U, (uint8_t)5U, (uint8_t)78U,
    (uint8_t)220U, (uint8_t)100U, (uint8_t)8U, (uint8_t)78U, (uint8_t)254U, (uint8_t)237U,
    (uint8_t)125U, (uint8_t)207U, (uint8_t)40U, (uint8_t)215U, (uint8_t)113U, (uint8_t)153U,
    (uint8_t)121U, (uint8_t)151U, (uint8_t)132U, (uint8_t)72U, (uint8_t)215U, (uint8_t)220U,
    (uint8_t)232U, (uint8_t)248U, (uint8_t)170U, (uint8_t)56U, (uint8_t)104U, (uint8_t)229U,
    (uint8_t)107U, (uint8_t)137U, (uint8_t)238U, (uint8_t)191U, (uint8_t)39U, (uint8_t)95U,
    (uint8_t)0U, (uint8_t)10U, (uint8_t)57U, (uint8_t)196U, (uint8_t)207U, (uint8_t)181U,
    (uint8_t)175U, (uint8_t)22U, (uint8_t)166U, (uint8_t)67U, (uint8_t)2U, (uint8_t)169U,
    (uint8_t)9U, (uint8_t)134U, (uint8_t)204U, (uint8_t)48U, (uint8_t)66U, (uint8_t)216U,
    (uint8_t)130U, (uint8_t)111U, (uint8_t)46U, (uint8_t)63U, (uint8_t)127U, (uint8_t)219U,
    (uint8_t)133U, (uint8_t)157U
  };

static uint8_t
vectors_low88[32U] =
  {
    (uint8_t)193U, (uint8_t)61U, (uint8_t)108U, (uint8_t)214U, (uint8_t)59U, (uint8_t)183U,
    (uint8_t)147U, (uint8_t)17U, (uint8_t)116U, (uint8_t)105U, (uint8_t)111U, (uint8_t)62U,
    (uint8_t)4U, (uint8_t)160U, (uint8_t)196U, (uint8_t)28U, (uint8_t)176U, (uint8_t)178U,
    (uint8_t)86U, (uint8_t)17U, (uint8_t)52U, (uint8_t)232U, (uint8_t)71U, (uint8_t)206U,
    (uint8_t)3U, (uint8_t)227U, (uint8_t)99U, (uint8_t)38U, (uint8_t)184U, (uint8_t)3U,
    (uint8_t)248U, (uint8_t)171U
  };

static uint8_t
vectors_low89[16U] =
  {
    (uint8_t)32U, (uint8_t)132U, (uint8_t)171U, (uint8_t)50U, (uint8_t)55U, (uint8_t)67U,
    (uint8_t)146U, (uint8_t)234U, (uint8_t)159U, (uint8_t)110U, (uint8_t)138U, (uint8_t)71U,
    (uint8_t)79U, (uint8_t)24U, (uint8_t)233U, (uint8_t)215U
  };

static uint8_t
vectors_low90[32U] =
  {
    (uint8_t)174U, (uint8_t)197U, (uint8_t)166U, (uint8_t)167U, (uint8_t)35U, (uint8_t)42U,
    (uint8_t)82U, (uint8_t)184U, (uint8_t)28U, (uint8_t)231U, (uint8_t)233U, (uint8_t)129U,
    (uint8_t)163U, (uint8_t)89U, (uint8_t)206U, (uint8_t)241U, (uint8_t)187U, (uint8_t)210U,
    (uint8_t)241U, (uint8_t)239U, (uint8_t)248U, (uint8_t)72U, (uint8_t)131U, (uint8_t)113U,
    (uint8_t)70U, (uint8_t)140U, (uint8_t)209U, (uint8_t)244U, (uint8_t)20U, (uint8_t)122U,
    (uint8_t)137U, (uint8_t)194U
  };

static uint8_t
vectors_low91[128U] =
  {
    (uint8_t)218U, (uint8_t)234U, (uint8_t)120U, (uint8_t)136U, (uint8_t)23U, (uint8_t)55U,
    (uint8_t)203U, (uint8_t)38U, (uint8_t)214U, (uint8_t)12U, (uint8_t)54U, (uint8_t)206U,
    (uint8_t)185U, (uint8_t)254U, (uint8_t)195U, (uint8_t)210U, (uint8_t)129U, (uint8_t)199U,
    (uint8_t)174U, (uint8_t)197U, (uint8_t)75U, (uint8_t)75U, (uint8_t)152U, (uint8_t)80U,
    (uint8_t)147U, (uint8_t)123U, (uint8_t)55U, (uint8_t)59U, (uint8_t)43U, (uint8_t)38U,
    (uint8_t)33U, (uint8_t)254U, (uint8_t)7U, (uint8_t)117U, (uint8_t)133U, (uint8_t)161U,
    (uint8_t)254U, (uint8_t)136U, (uint8_t)38U, (uint8_t)93U, (uint8_t)132U, (uint8_t)242U,
    (uint8_t)37U, (uint8_t)85U, (uint8_t)46U, (uint8_t)92U, (uint8_t)133U, (uint8_t)203U,
    (uint8_t)236U, (uint8_t)141U, (uint8_t)0U, (uint8_t)6U, (uint8_t)150U, (uint8_t)72U,
    (uint8_t)6U, (uint8_t)90U, (uint8_t)193U, (uint8_t)32U, (uint8_t)115U, (uint8_t)174U,
    (uint8_t)220U, (uint8_t)232U, (uint8_t)201U, (uint8_t)64U, (uint8_t)70U, (uint8_t)9U,
    (uint8_t)73U, (uint8_t)181U, (uint8_t)151U, (uint8_t)102U, (uint8_t)126U, (uint8_t)207U,
    (uint8_t)206U, (uint8_t)218U, (uint8_t)189U, (uint8_t)122U, (uint8_t)134U, (uint8_t)169U,
    (uint8_t)121U, (uint8_t)185U, (uint8_t)4U, (uint8_t)162U, (uint8_t)77U, (uint8_t)50U,
    (uint8_t)219U, (uint8_t)16U, (uint8_t)34U, (uint8_t)62U, (uint8_t)174U, (uint8_t)90U,
    (uint8_t)152U, (uint8_t)160U, (uint8_t)209U, (uint8_t)182U, (uint8_t)87U, (uint8_t)27U,
    (uint8_t)134U, (uint8_t)67U, (uint8_t)223U, (uint8_t)44U, (uint8_t)98U, (uint8_t)101U,
    (uint8_t)165U, (uint8_t)214U, (uint8_t)108U, (uint8_t)238U, (uint8_t)159U, (uint8_t)74U,
    (uint8_t)191U, (uint8_t)197U, (uint8_t)119U, (uint8_t)129U, (uint8_t)70U, (uint8_t)214U,
    (uint8_t)251U, (uint8_t)43U, (uint8_t)133U, (uint8_t)61U, (uint8_t)130U, (uint8_t)99U,
    (uint8_t)108U, (uint8_t)19U, (uint8_t)37U, (uint8_t)178U, (uint8_t)209U, (uint8_t)239U,
    (uint8_t)69U, (uint8_t)118U
  };

static uint8_t
vectors_low92[32U] =
  {
    (uint8_t)136U, (uint8_t)167U, (uint8_t)108U, (uint8_t)22U, (uint8_t)211U, (uint8_t)39U,
    (uint8_t)14U, (uint8_t)211U, (uint8_t)252U, (uint8_t)209U, (uint8_t)118U, (uint8_t)249U,
    (uint8_t)215U, (uint8_t)147U, (uint8_t)250U, (uint8_t)12U, (uint8_t)53U, (uint8_t)81U,
    (uint8_t)101U, (uint8_t)116U, (uint8_t)193U, (uint8_t)206U, (uint8_t)244U, (uint8_t)37U,
    (uint8_t)182U, (uint8_t)0U, (uint8_t)118U, (uint8_t)40U, (uint8_t)175U, (uint8_t)163U,
    (uint8_t)94U, (uint8_t)43U
  };

static uint8_t
vectors_low93[16U] =
  {
    (uint8_t)255U, (uint8_t)22U, (uint8_t)207U, (uint8_t)124U, (uint8_t)184U, (uint8_t)228U,
    (uint8_t)157U, (uint8_t)72U, (uint8_t)44U, (uint8_t)253U, (uint8_t)57U, (uint8_t)148U,
    (uint8_t)171U, (uint8_t)197U, (uint8_t)239U, (uint8_t)138U
  };

static uint8_t
vectors_low94[32U] =
  {
    (uint8_t)146U, (uint8_t)19U, (uint8_t)197U, (uint8_t)78U, (uint8_t)61U, (uint8_t)0U,
    (uint8_t)45U, (uint8_t)248U, (uint8_t)116U, (uint8_t)17U, (uint8_t)99U, (uint8_t)171U,
    (uint8_t)157U, (uint8_t)126U, (uint8_t)7U, (uint8_t)87U, (uint8_t)205U, (uint8_t)81U,
    (uint8_t)44U, (uint8_t)105U, (uint8_t)26U, (uint8_t)214U, (uint8_t)75U, (uint8_t)175U,
    (uint8_t)239U, (uint8_t)149U, (uint8_t)203U, (uint8_t)114U, (uint8_t)83U, (uint8_t)155U,
    (uint8_t)10U, (uint8_t)198U
  };

static uint8_t
vectors_low95[32U] =
  {
    (uint8_t)73U, (uint8_t)59U, (uint8_t)100U, (uint8_t)127U, (uint8_t)240U, (uint8_t)179U,
    (uint8_t)250U, (uint8_t)162U, (uint8_t)146U, (uint8_t)31U, (uint8_t)18U, (uint8_t)248U,
    (uint8_t)245U, (uint8_t)123U, (uint8_t)145U, (uint8_t)147U, (uint8_t)41U, (uint8_t)242U,
    (uint8_t)175U, (uint8_t)47U, (uint8_t)193U, (uint8_t)241U, (uint8_t)69U, (uint8_t)118U,
    (uint8_t)217U, (uint8_t)223U, (uint8_t)47U, (uint8_t)140U, (uint8_t)194U, (uint8_t)173U,
    (uint8_t)167U, (uint8_t)166U
  };

static uint8_t
vectors_low96[128U] =
  {
    (uint8_t)241U, (uint8_t)51U, (uint8_t)10U, (uint8_t)133U, (uint8_t)249U, (uint8_t)0U,
    (uint8_t)55U, (uint8_t)135U, (uint8_t)107U, (uint8_t)55U, (uint8_t)73U, (uint8_t)32U,
    (uint8_t)62U, (uint8_t)132U, (uint8_t)146U, (uint8_t)135U, (uint8_t)68U, (uint8_t)74U,
    (uint8_t)130U, (uint8_t)127U, (uint8_t)10U, (uint8_t)88U, (uint8_t)194U, (uint8_t)73U,
    (uint8_t)255U, (uint8_t)134U, (uint8_t)143U, (uint8_t)193U, (uint8_t)173U, (uint8_t)186U,
    (uint8_t)77U, (uint8_t)206U, (uint8_t)40U, (uint8_t)94U, (uint8_t)7U, (uint8_t)106U,
    (uint8_t)31U, (uint8_t)138U, (uint8_t)225U, (uint8_t)218U, (uint8_t)140U, (uint8_t)249U,
    (uint8_t)254U, (uint8_t)20U, (uint8_t)147U, (uint8_t)30U, (uint8_t)129U, (uint8_t)100U,
    (uint8_t)24U, (uint8_t)108U, (uint8_t)151U, (uint8_t)168U, (uint8_t)254U, (uint8_t)175U,
    (uint8_t)36U, (uint8_t)88U, (uint8_t)52U, (uint8_t)81U, (uint8_t)241U, (uint8_t)22U,
    (uint8_t)230U, (uint8_t)95U, (uint8_t)142U, (uint8_t)67U, (uint8_t)46U, (uint8_t)126U,
    (uint8_t)213U, (uint8_t)90U, (uint8_t)54U, (uint8_t)104U, (uint8_t)49U, (uint8_t)32U,
    (uint8_t)55U, (uint8_t)126U, (uint8_t)35U, (uint8_t)18U, (uint8_t)141U, (uint8_t)202U,
    (uint8_t)21U, (uint8_t)64U, (uint8_t)254U, (uint8_t)251U, (uint8_t)243U, (uint8_t)175U,
    (uint8_t)27U, (uint8_t)86U, (uint8_t)213U, (uint8_t)199U, (uint8_t)65U, (uint8_t)135U,
    (uint8_t)245U, (uint8_t)40U, (uint8_t)109U, (uint8_t)10U, (uint8_t)149U, (uint8_t)251U,
    (uint8_t)85U, (uint8_t)147U, (uint8_t)23U, (uint8_t)112U, (uint8_t)84U, (uint8_t)48U,
    (uint8_t)96U, (uint8_t)206U, (uint8_t)141U, (uint8_t)240U, (uint8_t)143U, (uint8_t)60U,
    (uint8_t)25U, (uint8_t)89U, (uint8_t)161U, (uint8_t)244U, (uint8_t)252U, (uint8_t)54U,
    (uint8_t)182U, (uint8_t)70U, (uint8_t)113U, (uint8_t)224U, (uint8_t)101U, (uint8_t)79U,
    (uint8_t)255U, (uint8_t)231U, (uint8_t)13U, (uint8_t)150U, (uint8_t)213U, (uint8_t)33U,
    (uint8_t)190U, (uint8_t)33U
  };

static uint8_t
vectors_low97[32U] =
  {
    (uint8_t)232U, (uint8_t)233U, (uint8_t)159U, (uint8_t)252U, (uint8_t)240U, (uint8_t)138U,
    (uint8_t)173U, (uint8_t)142U, (uint8_t)80U, (uint8_t)56U, (uint8_t)111U, (uint8_t)93U,
    (uint8_t)7U, (uint8_t)157U, (uint8_t)121U, (uint8_t)211U, (uint8_t)219U, (uint8_t)120U,
    (uint8_t)58U, (uint8_t)116U, (uint8_t)22U, (uint8_t)92U, (uint8_t)97U, (uint8_t)38U,
    (uint8_t)180U, (uint8_t)43U, (uint8_t)49U, (uint8_t)64U, (uint8_t)247U, (uint8_t)68U,
    (uint8_t)167U, (uint8_t)199U
  };

static uint8_t
vectors_low98[16U] =
  {
    (uint8_t)35U, (uint8_t)84U, (uint8_t)25U, (uint8_t)48U, (uint8_t)200U, (uint8_t)199U,
    (uint8_t)114U, (uint8_t)173U, (uint8_t)182U, (uint8_t)41U, (uint8_t)129U, (uint8_t)219U,
    (uint8_t)239U, (uint8_t)141U, (uint8_t)5U, (uint8_t)78U
  };

static uint8_t
vectors_low99[32U] =
  {
    (uint8_t)205U, (uint8_t)207U, (uint8_t)28U, (uint8_t)48U, (uint8_t)34U, (uint8_t)137U,
    (uint8_t)4U, (uint8_t)189U, (uint8_t)123U, (uint8_t)163U, (uint8_t)23U, (uint8_t)152U,
    (uint8_t)191U, (uint8_t)187U, (uint8_t)214U, (uint8_t)71U, (uint8_t)87U, (uint8_t)170U,
    (uint8_t)37U, (uint8_t)26U, (uint8_t)201U, (uint8_t)161U, (uint8_t)174U, (uint8_t)140U,
    (uint8_t)32U, (uint8_t)160U, (uint8_t)80U, (uint8_t)103U, (uint8_t)15U, (uint8_t)234U,
    (uint8_t)197U, (uint8_t)155U
  };

static uint8_t
vectors_low100[32U] =
  {
    (uint8_t)84U, (uint8_t)110U, (uint8_t)4U, (uint8_t)36U, (uint8_t)125U, (uint8_t)108U,
    (uint8_t)181U, (uint8_t)33U, (uint8_t)42U, (uint8_t)87U, (uint8_t)182U, (uint8_t)47U,
    (uint8_t)153U, (uint8_t)225U, (uint8_t)204U, (uint8_t)167U, (uint8_t)103U, (uint8_t)165U,
    (uint8_t)118U, (uint8_t)140U, (uint8_t)247U, (uint8_t)146U, (uint8_t)150U, (uint8_t)244U,
    (uint8_t)95U, (uint8_t)13U, (uint8_t)178U, (uint8_t)71U, (uint8_t)50U, (uint8_t)186U,
    (uint8_t)99U, (uint8_t)104U
  };

static uint8_t
vectors_low101[32U] =
  {
    (uint8_t)253U, (uint8_t)69U, (uint8_t)246U, (uint8_t)108U, (uint8_t)141U, (uint8_t)237U,
    (uint8_t)228U, (uint8_t)19U, (uint8_t)135U, (uint8_t)55U, (uint8_t)60U, (uint8_t)56U,
    (uint8_t)103U, (uint8_t)70U, (uint8_t)5U, (uint8_t)243U, (uint8_t)224U, (uint8_t)117U,
    (uint8_t)201U, (uint8_t)183U, (uint8_t)207U, (uint8_t)198U, (uint8_t)97U, (uint8_t)35U,
    (uint8_t)165U, (uint8_t)71U, (uint8_t)139U, (uint8_t)143U, (uint8_t)142U, (uint8_t)58U,
    (uint8_t)178U, (uint8_t)118U
  };

static uint8_t
vectors_low102[32U] =
  {
    (uint8_t)57U, (uint8_t)145U, (uint8_t)26U, (uint8_t)121U, (uint8_t)198U, (uint8_t)237U,
    (uint8_t)187U, (uint8_t)200U, (uint8_t)5U, (uint8_t)165U, (uint8_t)13U, (uint8_t)42U,
    (uint8_t)160U, (uint8_t)24U, (uint8_t)116U, (uint8_t)32U, (uint8_t)148U, (uint8_t)23U,
    (uint8_t)122U, (uint8_t)142U, (uint8_t)33U, (uint8_t)109U, (uint8_t)100U, (uint8_t)124U,
    (uint8_t)100U, (uint8_t)66U, (uint8_t)140U, (uint8_t)0U, (uint8_t)22U, (uint8_t)154U,
    (uint8_t)178U, (uint8_t)214U
  };

static uint8_t
vectors_low103[192U] =
  {
    (uint8_t)135U, (uint8_t)21U, (uint8_t)119U, (uint8_t)221U, (uint8_t)243U, (uint8_t)75U,
    (uint8_t)41U, (uint8_t)229U, (uint8_t)202U, (uint8_t)241U, (uint8_t)50U, (uint8_t)170U,
    (uint8_t)130U, (uint8_t)225U, (uint8_t)210U, (uint8_t)241U, (uint8_t)88U, (uint8_t)107U,
    (uint8_t)118U, (uint8_t)227U, (uint8_t)154U, (uint8_t)171U, (uint8_t)98U, (uint8_t)172U,
    (uint8_t)208U, (uint8_t)47U, (uint8_t)109U, (uint8_t)68U, (uint8_t)64U, (uint8_t)144U,
    (uint8_t)138U, (uint8_t)119U, (uint8_t)42U, (uint8_t)197U, (uint8_t)246U, (uint8_t)253U,
    (uint8_t)72U, (uint8_t)197U, (uint8_t)245U, (uint8_t)95U, (uint8_t)30U, (uint8_t)190U,
    (uint8_t)14U, (uint8_t)118U, (uint8_t)34U, (uint8_t)26U, (uint8_t)196U, (uint8_t)107U,
    (uint8_t)131U, (uint8_t)74U, (uint8_t)138U, (uint8_t)79U, (uint8_t)93U, (uint8_t)217U,
    (uint8_t)149U, (uint8_t)135U, (uint8_t)33U, (uint8_t)238U, (uint8_t)5U, (uint8_t)59U,
    (uint8_t)163U, (uint8_t)174U, (uint8_t)241U, (uint8_t)87U, (uint8_t)78U, (uint8_t)189U,
    (uint8_t)152U, (uint8_t)10U, (uint8_t)93U, (uint8_t)166U, (uint8_t)169U, (uint8_t)70U,
    (uint8_t)147U, (uint8_t)102U, (uint8_t)39U, (uint8_t)23U, (uint8_t)238U, (uint8_t)84U,
    (uint8_t)138U, (uint8_t)240U, (uint8_t)249U, (uint8_t)33U, (uint8_t)66U, (uint8_t)29U,
    (uint8_t)26U, (uint8_t)251U, (uint8_t)129U, (uint8_t)78U, (uint8_t)77U, (uint8_t)23U,
    (uint8_t)153U, (uint8_t)211U, (uint8_t)81U, (uint8_t)136U, (uint8_t)157U, (uint8_t)42U,
    (uint8_t)27U, (uint8_t)221U, (uint8_t)87U, (uint8_t)87U, (uint8_t)10U, (uint8_t)145U,
    (uint8_t)62U, (uint8_t)66U, (uint8_t)142U, (uint8_t)102U, (uint8_t)19U, (uint8_t)177U,
    (uint8_t)110U, (uint8_t)21U, (uint8_t)140U, (uint8_t)28U, (uint8_t)254U, (uint8_t)208U,
    (uint8_t)56U, (uint8_t)246U, (uint8_t)87U, (uint8_t)137U, (uint8_t)32U, (uint8_t)214U,
    (uint8_t)13U, (uint8_t)183U, (uint8_t)61U, (uint8_t)193U, (uint8_t)10U, (uint8_t)64U,
    (uint8_t)218U, (uint8_t)155U, (uint8_t)195U, (uint8_t)99U, (uint8_t)160U, (uint8_t)32U,
    (uint8_t)107U, (uint8_t)78U, (uint8_t)126U, (uint8_t)73U, (uint8_t)103U, (uint8_t)14U,
    (uint8_t)204U, (uint8_t)234U, (uint8_t)134U, (uint8_t)110U, (uint8_t)253U, (uint8_t)154U,
    (uint8_t)5U, (uint8_t)188U, (uint8_t)35U, (uint8_t)112U, (uint8_t)66U, (uint8_t)207U,
    (uint8_t)5U, (uint8_t)47U, (uint8_t)42U, (uint8_t)65U, (uint8_t)64U, (uint8_t)249U,
    (uint8_t)55U, (uint8_t)126U, (uint8_t)60U, (uint8_t)103U, (uint8_t)146U, (uint8_t)184U,
    (uint8_t)142U, (uint8_t)160U, (uint8_t)99U, (uint8_t)35U, (uint8_t)252U, (uint8_t)235U,
    (uint8_t)185U, (uint8_t)156U, (uint8_t)100U, (uint8_t)63U, (uint8_t)193U, (uint8_t)195U,
    (uint8_t)101U, (uint8_t)55U, (uint8_t)88U, (uint8_t)214U, (uint8_t)134U, (uint8_t)108U,
    (uint8_t)219U, (uint8_t)20U, (uint8_t)136U, (uint8_t)55U, (uint8_t)251U, (uint8_t)15U,
    (uint8_t)223U, (uint8_t)119U, (uint8_t)222U, (uint8_t)21U, (uint8_t)100U, (uint8_t)207U
  };

static uint8_t
vectors_low104[32U] =
  {
    (uint8_t)147U, (uint8_t)25U, (uint8_t)20U, (uint8_t)143U, (uint8_t)183U, (uint8_t)194U,
    (uint8_t)56U, (uint8_t)151U, (uint8_t)147U, (uint8_t)233U, (uint8_t)245U, (uint8_t)60U,
    (uint8_t)211U, (uint8_t)180U, (uint8_t)173U, (uint8_t)143U, (uint8_t)27U, (uint8_t)183U,
    (uint8_t)87U, (uint8_t)16U, (uint8_t)8U, (uint8_t)143U, (uint8_t)28U, (uint8_t)154U,
    (uint8_t)24U, (uint8_t)67U, (uint8_t)76U, (uint8_t)225U, (uint8_t)59U, (uint8_t)25U,
    (uint8_t)13U, (uint8_t)162U
  };

static uint8_t
vectors_low105[16U] =
  {
    (uint8_t)17U, (uint8_t)253U, (uint8_t)197U, (uint8_t)60U, (uint8_t)19U, (uint8_t)174U,
    (uint8_t)163U, (uint8_t)57U, (uint8_t)133U, (uint8_t)186U, (uint8_t)38U, (uint8_t)120U,
    (uint8_t)232U, (uint8_t)216U, (uint8_t)109U, (uint8_t)9U
  };

static uint8_t
vectors_low106[32U] =
  {
    (uint8_t)134U, (uint8_t)25U, (uint8_t)41U, (uint8_t)14U, (uint8_t)151U, (uint8_t)95U,
    (uint8_t)28U, (uint8_t)80U, (uint8_t)246U, (uint8_t)96U, (uint8_t)108U, (uint8_t)112U,
    (uint8_t)39U, (uint8_t)239U, (uint8_t)233U, (uint8_t)200U, (uint8_t)67U, (uint8_t)141U,
    (uint8_t)50U, (uint8_t)9U, (uint8_t)219U, (uint8_t)113U, (uint8_t)237U, (uint8_t)208U,
    (uint8_t)35U, (uint8_t)175U, (uint8_t)14U, (uint8_t)176U, (uint8_t)36U, (uint8_t)162U,
    (uint8_t)130U, (uint8_t)210U
  };

static uint8_t
vectors_low107[192U] =
  {
    (uint8_t)48U, (uint8_t)194U, (uint8_t)50U, (uint8_t)126U, (uint8_t)221U, (uint8_t)181U,
    (uint8_t)195U, (uint8_t)148U, (uint8_t)45U, (uint8_t)144U, (uint8_t)0U, (uint8_t)110U,
    (uint8_t)173U, (uint8_t)204U, (uint8_t)252U, (uint8_t)38U, (uint8_t)210U, (uint8_t)123U,
    (uint8_t)20U, (uint8_t)159U, (uint8_t)25U, (uint8_t)83U, (uint8_t)137U, (uint8_t)171U,
    (uint8_t)186U, (uint8_t)80U, (uint8_t)124U, (uint8_t)7U, (uint8_t)70U, (uint8_t)228U,
    (uint8_t)29U, (uint8_t)127U, (uint8_t)184U, (uint8_t)207U, (uint8_t)48U, (uint8_t)193U,
    (uint8_t)95U, (uint8_t)44U, (uint8_t)223U, (uint8_t)247U, (uint8_t)63U, (uint8_t)243U,
    (uint8_t)215U, (uint8_t)123U, (uint8_t)76U, (uint8_t)160U, (uint8_t)210U, (uint8_t)137U,
    (uint8_t)240U, (uint8_t)102U, (uint8_t)0U, (uint8_t)115U, (uint8_t)242U, (uint8_t)199U,
    (uint8_t)63U, (uint8_t)131U, (uint8_t)206U, (uint8_t)129U, (uint8_t)154U, (uint8_t)106U,
    (uint8_t)125U, (uint8_t)143U, (uint8_t)233U, (uint8_t)17U, (uint8_t)253U, (uint8_t)16U,
    (uint8_t)151U, (uint8_t)120U, (uint8_t)181U, (uint8_t)1U, (uint8_t)53U, (uint8_t)126U,
    (uint8_t)202U, (uint8_t)115U, (uint8_t)7U, (uint8_t)157U, (uint8_t)134U, (uint8_t)190U,
    (uint8_t)208U, (uint8_t)145U, (uint8_t)109U, (uint8_t)238U, (uint8_t)222U, (uint8_t)84U,
    (uint8_t)226U, (uint8_t)232U, (uint8_t)110U, (uint8_t)202U, (uint8_t)44U, (uint8_t)4U,
    (uint8_t)243U, (uint8_t)208U, (uint8_t)112U, (uint8_t)110U, (uint8_t)42U, (uint8_t)85U,
    (uint8_t)255U, (uint8_t)132U, (uint8_t)148U, (uint8_t)44U, (uint8_t)191U, (uint8_t)238U,
    (uint8_t)34U, (uint8_t)181U, (uint8_t)169U, (uint8_t)45U, (uint8_t)48U, (uint8_t)155U,
    (uint8_t)132U, (uint8_t)184U, (uint8_t)221U, (uint8_t)61U, (uint8_t)236U, (uint8_t)185U,
    (uint8_t)243U, (uint8_t)242U, (uint8_t)196U, (uint8_t)178U, (uint8_t)78U, (uint8_t)251U,
    (uint8_t)79U, (uint8_t)56U, (uint8_t)40U, (uint8_t)51U, (uint8_t)255U, (uint8_t)184U,
    (uint8_t)103U, (uint8_t)181U, (uint8_t)254U, (uint8_t)5U, (uint8_t)75U, (uint8_t)33U,
    (uint8_t)212U, (uint8_t)125U, (uint8_t)182U, (uint8_t)197U, (uint8_t)47U, (uint8_t)245U,
    (uint8_t)47U, (uint8_t)170U, (uint8_t)19U, (uint8_t)206U, (uint8_t)42U, (uint8_t)189U,
    (uint8_t)247U, (uint8_t)153U, (uint8_t)110U, (uint8_t)35U, (uint8_t)168U, (uint8_t)201U,
    (uint8_t)107U, (uint8_t)172U, (uint8_t)72U, (uint8_t)192U, (uint8_t)41U, (uint8_t)128U,
    (uint8_t)217U, (uint8_t)98U, (uint8_t)52U, (uint8_t)228U, (uint8_t)120U, (uint8_t)55U,
    (uint8_t)0U, (uint8_t)39U, (uint8_t)213U, (uint8_t)91U, (uint8_t)168U, (uint8_t)117U,
    (uint8_t)44U, (uint8_t)23U, (uint8_t)199U, (uint8_t)161U, (uint8_t)191U, (uint8_t)98U,
    (uint8_t)83U, (uint8_t)8U, (uint8_t)70U, (uint8_t)84U, (uint8_t)231U, (uint8_t)156U,
    (uint8_t)19U, (uint8_t)186U, (uint8_t)204U, (uint8_t)81U, (uint8_t)193U, (uint8_t)129U,
    (uint8_t)92U, (uint8_t)139U, (uint8_t)100U, (uint8_t)126U, (uint8_t)54U, (uint8_t)203U
  };

static uint8_t
vectors_low108[32U] =
  {
    (uint8_t)249U, (uint8_t)226U, (uint8_t)80U, (uint8_t)96U, (uint8_t)103U, (uint8_t)94U,
    (uint8_t)76U, (uint8_t)87U, (uint8_t)52U, (uint8_t)216U, (uint8_t)24U, (uint8_t)217U,
    (uint8_t)195U, (uint8_t)26U, (uint8_t)11U, (uint8_t)35U, (uint8_t)36U, (uint8_t)116U,
    (uint8_t)82U, (uint8_t)5U, (uint8_t)119U, (uint8_t)228U, (uint8_t)47U, (uint8_t)140U,
    (uint8_t)83U, (uint8_t)248U, (uint8_t)3U, (uint8_t)174U, (uint8_t)226U, (uint8_t)52U,
    (uint8_t)159U, (uint8_t)74U
  };

static uint8_t
vectors_low109[16U] =
  {
    (uint8_t)154U, (uint8_t)98U, (uint8_t)164U, (uint8_t)28U, (uint8_t)243U, (uint8_t)245U,
    (uint8_t)169U, (uint8_t)225U, (uint8_t)152U, (uint8_t)223U, (uint8_t)248U, (uint8_t)201U,
    (uint8_t)7U, (uint8_t)163U, (uint8_t)90U, (uint8_t)63U
  };

static uint8_t
vectors_low110[32U] =
  {
    (uint8_t)136U, (uint8_t)138U, (uint8_t)117U, (uint8_t)41U, (uint8_t)144U, (uint8_t)154U,
    (uint8_t)227U, (uint8_t)96U, (uint8_t)83U, (uint8_t)199U, (uint8_t)91U, (uint8_t)173U,
    (uint8_t)180U, (uint8_t)77U, (uint8_t)16U, (uint8_t)49U, (uint8_t)24U, (uint8_t)225U,
    (uint8_t)113U, (uint8_t)120U, (uint8_t)74U, (uint8_t)123U, (uint8_t)103U, (uint8_t)220U,
    (uint8_t)13U, (uint8_t)122U, (uint8_t)78U, (uint8_t)27U, (uint8_t)29U, (uint8_t)68U,
    (uint8_t)57U, (uint8_t)26U
  };

static uint8_t
vectors_low111[32U] =
  {
    (uint8_t)16U, (uint8_t)162U, (uint8_t)93U, (uint8_t)0U, (uint8_t)39U, (uint8_t)177U,
    (uint8_t)197U, (uint8_t)95U, (uint8_t)97U, (uint8_t)93U, (uint8_t)59U, (uint8_t)124U,
    (uint8_t)63U, (uint8_t)35U, (uint8_t)93U, (uint8_t)121U, (uint8_t)26U, (uint8_t)129U,
    (uint8_t)223U, (uint8_t)232U, (uint8_t)33U, (uint8_t)83U, (uint8_t)21U, (uint8_t)224U,
    (uint8_t)195U, (uint8_t)143U, (uint8_t)204U, (uint8_t)222U, (uint8_t)39U, (uint8_t)165U,
    (uint8_t)216U, (uint8_t)218U
  };

static uint8_t
vectors_low112[32U] =
  {
    (uint8_t)123U, (uint8_t)16U, (uint8_t)226U, (uint8_t)80U, (uint8_t)68U, (uint8_t)171U,
    (uint8_t)208U, (uint8_t)145U, (uint8_t)116U, (uint8_t)144U, (uint8_t)231U, (uint8_t)241U,
    (uint8_t)168U, (uint8_t)207U, (uint8_t)210U, (uint8_t)73U, (uint8_t)102U, (uint8_t)128U,
    (uint8_t)63U, (uint8_t)201U, (uint8_t)190U, (uint8_t)38U, (uint8_t)15U, (uint8_t)58U,
    (uint8_t)181U, (uint8_t)191U, (uint8_t)149U, (uint8_t)70U, (uint8_t)147U, (uint8_t)246U,
    (uint8_t)8U, (uint8_t)133U
  };

static uint8_t
vectors_low113[32U] =
  {
    (uint8_t)163U, (uint8_t)86U, (uint8_t)62U, (uint8_t)197U, (uint8_t)192U, (uint8_t)137U,
    (uint8_t)255U, (uint8_t)241U, (uint8_t)39U, (uint8_t)178U, (uint8_t)162U, (uint8_t)234U,
    (uint8_t)239U, (uint8_t)18U, (uint8_t)189U, (uint8_t)12U, (uint8_t)179U, (uint8_t)177U,
    (uint8_t)143U, (uint8_t)58U, (uint8_t)9U, (uint8_t)153U, (uint8_t)117U, (uint8_t)70U,
    (uint8_t)102U, (uint8_t)17U, (uint8_t)58U, (uint8_t)5U, (uint8_t)47U, (uint8_t)212U,
    (uint8_t)67U, (uint8_t)249U
  };

static uint8_t
vectors_low114[192U] =
  {
    (uint8_t)131U, (uint8_t)185U, (uint8_t)254U, (uint8_t)244U, (uint8_t)243U, (uint8_t)28U,
    (uint8_t)113U, (uint8_t)174U, (uint8_t)191U, (uint8_t)55U, (uint8_t)83U, (uint8_t)208U,
    (uint8_t)64U, (uint8_t)66U, (uint8_t)8U, (uint8_t)103U, (uint8_t)137U, (uint8_t)135U,
    (uint8_t)252U, (uint8_t)76U, (uint8_t)178U, (uint8_t)210U, (uint8_t)147U, (uint8_t)168U,
    (uint8_t)172U, (uint8_t)138U, (uint8_t)84U, (uint8_t)122U, (uint8_t)237U, (uint8_t)24U,
    (uint8_t)167U, (uint8_t)169U, (uint8_t)224U, (uint8_t)157U, (uint8_t)129U, (uint8_t)150U,
    (uint8_t)160U, (uint8_t)125U, (uint8_t)110U, (uint8_t)151U, (uint8_t)201U, (uint8_t)9U,
    (uint8_t)230U, (uint8_t)74U, (uint8_t)239U, (uint8_t)0U, (uint8_t)217U, (uint8_t)185U,
    (uint8_t)83U, (uint8_t)12U, (uint8_t)161U, (uint8_t)205U, (uint8_t)105U, (uint8_t)214U,
    (uint8_t)88U, (uint8_t)7U, (uint8_t)133U, (uint8_t)125U, (uint8_t)155U, (uint8_t)48U,
    (uint8_t)167U, (uint8_t)73U, (uint8_t)36U, (uint8_t)166U, (uint8_t)190U, (uint8_t)150U,
    (uint8_t)221U, (uint8_t)150U, (uint8_t)252U, (uint8_t)72U, (uint8_t)173U, (uint8_t)89U,
    (uint8_t)49U, (uint8_t)137U, (uint8_t)39U, (uint8_t)54U, (uint8_t)167U, (uint8_t)127U,
    (uint8_t)98U, (uint8_t)246U, (uint8_t)140U, (uint8_t)63U, (uint8_t)202U, (uint8_t)117U,
    (uint8_t)175U, (uint8_t)62U, (uint8_t)46U, (uint8_t)165U, (uint8_t)178U, (uint8_t)163U,
    (uint8_t)54U, (uint8_t)241U, (uint8_t)224U, (uint8_t)128U, (uint8_t)162U, (uint8_t)79U,
    (uint8_t)162U, (uint8_t)143U, (uint8_t)129U, (uint8_t)253U, (uint8_t)139U, (uint8_t)26U,
    (uint8_t)52U, (uint8_t)211U, (uint8_t)200U, (uint8_t)170U, (uint8_t)198U, (uint8_t)80U,
    (uint8_t)172U, (uint8_t)170U, (uint8_t)210U, (uint8_t)94U, (uint8_t)209U, (uint8_t)224U,
    (uint8_t)11U, (uint8_t)196U, (uint8_t)64U, (uint8_t)146U, (uint8_t)161U, (uint8_t)57U,
    (uint8_t)64U, (uint8_t)200U, (uint8_t)33U, (uint8_t)148U, (uint8_t)42U, (uint8_t)221U,
    (uint8_t)24U, (uint8_t)191U, (uint8_t)14U, (uint8_t)215U, (uint8_t)12U, (uint8_t)87U,
    (uint8_t)140U, (uint8_t)48U, (uint8_t)87U, (uint8_t)17U, (uint8_t)176U, (uint8_t)164U,
    (uint8_t)153U, (uint8_t)30U, (uint8_t)197U, (uint8_t)189U, (uint8_t)223U, (uint8_t)174U,
    (uint8_t)206U, (uint8_t)232U, (uint8_t)4U, (uint8_t)97U, (uint8_t)155U, (uint8_t)25U,
    (uint8_t)127U, (uint8_t)215U, (uint8_t)22U, (uint8_t)170U, (uint8_t)46U, (uint8_t)103U,
    (uint8_t)19U, (uint8_t)192U, (uint8_t)207U, (uint8_t)145U, (uint8_t)234U, (uint8_t)10U,
    (uint8_t)109U, (uint8_t)70U, (uint8_t)164U, (uint8_t)208U, (uint8_t)234U, (uint8_t)128U,
    (uint8_t)167U, (uint8_t)247U, (uint8_t)15U, (uint8_t)79U, (uint8_t)199U, (uint8_t)83U,
    (uint8_t)7U, (uint8_t)211U, (uint8_t)66U, (uint8_t)230U, (uint8_t)157U, (uint8_t)31U,
    (uint8_t)223U, (uint8_t)249U, (uint8_t)137U, (uint8_t)128U, (uint8_t)139U, (uint8_t)117U,
    (uint8_t)0U, (uint8_t)39U, (uint8_t)92U, (uint8_t)208U, (uint8_t)82U, (uint8_t)24U
  };

static uint8_t
vectors_low115[32U] =
  {
    (uint8_t)88U, (uint8_t)235U, (uint8_t)206U, (uint8_t)196U, (uint8_t)83U, (uint8_t)159U,
    (uint8_t)74U, (uint8_t)241U, (uint8_t)179U, (uint8_t)42U, (uint8_t)133U, (uint8_t)65U,
    (uint8_t)129U, (uint8_t)221U, (uint8_t)15U, (uint8_t)81U, (uint8_t)43U, (uint8_t)140U,
    (uint8_t)112U, (uint8_t)79U, (uint8_t)164U, (uint8_t)117U, (uint8_t)55U, (uint8_t)9U,
    (uint8_t)106U, (uint8_t)118U, (uint8_t)158U, (uint8_t)255U, (uint8_t)40U, (uint8_t)197U,
    (uint8_t)145U, (uint8_t)101U
  };

static uint8_t
vectors_low116[16U] =
  {
    (uint8_t)161U, (uint8_t)130U, (uint8_t)38U, (uint8_t)207U, (uint8_t)199U, (uint8_t)121U,
    (uint8_t)239U, (uint8_t)201U, (uint8_t)85U, (uint8_t)15U, (uint8_t)123U, (uint8_t)224U,
    (uint8_t)32U, (uint8_t)6U, (uint8_t)216U, (uint8_t)60U
  };

static uint8_t
vectors_low117[32U] =
  {
    (uint8_t)35U, (uint8_t)12U, (uint8_t)214U, (uint8_t)230U, (uint8_t)144U, (uint8_t)158U,
    (uint8_t)48U, (uint8_t)29U, (uint8_t)30U, (uint8_t)153U, (uint8_t)236U, (uint8_t)209U,
    (uint8_t)255U, (uint8_t)242U, (uint8_t)178U, (uint8_t)205U, (uint8_t)0U, (uint8_t)165U,
    (uint8_t)108U, (uint8_t)122U, (uint8_t)104U, (uint8_t)76U, (uint8_t)137U, (uint8_t)7U,
    (uint8_t)187U, (uint8_t)177U, (uint8_t)60U, (uint8_t)227U, (uint8_t)233U, (uint8_t)160U,
    (uint8_t)203U, (uint8_t)206U
  };

static uint8_t
vectors_low118[256U] =
  {
    (uint8_t)111U, (uint8_t)78U, (uint8_t)134U, (uint8_t)243U, (uint8_t)9U, (uint8_t)246U,
    (uint8_t)145U, (uint8_t)68U, (uint8_t)96U, (uint8_t)57U, (uint8_t)97U, (uint8_t)197U,
    (uint8_t)54U, (uint8_t)110U, (uint8_t)79U, (uint8_t)155U, (uint8_t)22U, (uint8_t)209U,
    (uint8_t)12U, (uint8_t)16U, (uint8_t)89U, (uint8_t)62U, (uint8_t)166U, (uint8_t)137U,
    (uint8_t)168U, (uint8_t)231U, (uint8_t)67U, (uint8_t)90U, (uint8_t)50U, (uint8_t)125U,
    (uint8_t)37U, (uint8_t)36U, (uint8_t)244U, (uint8_t)70U, (uint8_t)136U, (uint8_t)19U,
    (uint8_t)234U, (uint8_t)127U, (uint8_t)50U, (uint8_t)72U, (uint8_t)216U, (uint8_t)212U,
    (uint8_t)187U, (uint8_t)225U, (uint8_t)123U, (uint8_t)23U, (uint8_t)92U, (uint8_t)252U,
    (uint8_t)64U, (uint8_t)97U, (uint8_t)113U, (uint8_t)73U, (uint8_t)152U, (uint8_t)57U,
    (uint8_t)40U, (uint8_t)178U, (uint8_t)103U, (uint8_t)220U, (uint8_t)12U, (uint8_t)77U,
    (uint8_t)180U, (uint8_t)109U, (uint8_t)44U, (uint8_t)23U, (uint8_t)254U, (uint8_t)139U,
    (uint8_t)192U, (uint8_t)118U, (uint8_t)67U, (uint8_t)134U, (uint8_t)117U, (uint8_t)138U,
    (uint8_t)241U, (uint8_t)168U, (uint8_t)36U, (uint8_t)225U, (uint8_t)46U, (uint8_t)184U,
    (uint8_t)151U, (uint8_t)254U, (uint8_t)175U, (uint8_t)193U, (uint8_t)199U, (uint8_t)239U,
    (uint8_t)102U, (uint8_t)248U, (uint8_t)15U, (uint8_t)252U, (uint8_t)217U, (uint8_t)147U,
    (uint8_t)170U, (uint8_t)1U, (uint8_t)110U, (uint8_t)19U, (uint8_t)153U, (uint8_t)145U,
    (uint8_t)205U, (uint8_t)232U, (uint8_t)67U, (uint8_t)94U, (uint8_t)230U, (uint8_t)187U,
    (uint8_t)13U, (uint8_t)228U, (uint8_t)90U, (uint8_t)127U, (uint8_t)182U, (uint8_t)30U,
    (uint8_t)177U, (uint8_t)166U, (uint8_t)190U, (uint8_t)183U, (uint8_t)110U, (uint8_t)1U,
    (uint8_t)43U, (uint8_t)132U, (uint8_t)142U, (uint8_t)160U, (uint8_t)3U, (uint8_t)246U,
    (uint8_t)135U, (uint8_t)83U, (uint8_t)126U, (uint8_t)75U, (uint8_t)208U, (uint8_t)12U,
    (uint8_t)237U, (uint8_t)55U, (uint8_t)239U, (uint8_t)221U, (uint8_t)166U, (uint8_t)99U,
    (uint8_t)51U, (uint8_t)181U, (uint8_t)58U, (uint8_t)141U, (uint8_t)213U, (uint8_t)34U,
    (uint8_t)12U, (uint8_t)40U, (uint8_t)31U, (uint8_t)191U, (uint8_t)104U, (uint8_t)191U,
    (uint8_t)217U, (uint8_t)231U, (uint8_t)34U, (uint8_t)133U, (uint8_t)231U, (uint8_t)129U,
    (uint8_t)151U, (uint8_t)136U, (uint8_t)30U, (uint8_t)252U, (uint8_t)84U, (uint8_t)13U,
    (uint8_t)164U, (uint8_t)193U, (uint8_t)186U, (uint8_t)128U, (uint8_t)162U, (uint8_t)38U,
    (uint8_t)1U, (uint8_t)58U, (uint8_t)45U, (uint8_t)112U, (uint8_t)152U, (uint8_t)211U,
    (uint8_t)74U, (uint8_t)244U, (uint8_t)17U, (uint8_t)46U, (uint8_t)123U, (uint8_t)140U,
    (uint8_t)134U, (uint8_t)90U, (uint8_t)241U, (uint8_t)84U, (uint8_t)9U, (uint8_t)246U,
    (uint8_t)144U, (uint8_t)27U, (uint8_t)149U, (uint8_t)47U, (uint8_t)238U, (uint8_t)74U,
    (uint8_t)71U, (uint8_t)78U, (uint8_t)64U, (uint8_t)39U, (uint8_t)5U, (uint8_t)30U, (uint8_t)29U,
    (uint8_t)206U, (uint8_t)135U, (uint8_t)157U, (uint8_t)223U, (uint8_t)94U, (uint8_t)132U,
    (uint8_t)243U, (uint8_t)148U, (uint8_t)125U, (uint8_t)201U, (uint8_t)185U, (uint8_t)65U,
    (uint8_t)25U, (uint8_t)214U, (uint8_t)126U, (uint8_t)107U, (uint8_t)72U, (uint8_t)237U,
    (uint8_t)111U, (uint8_t)214U, (uint8_t)177U, (uint8_t)248U, (uint8_t)19U, (uint8_t)193U,
    (uint8_t)61U, (uint8_t)63U, (uint8_t)243U, (uint8_t)14U, (uint8_t)18U, (uint8_t)30U,
    (uint8_t)252U, (uint8_t)231U, (uint8_t)145U, (uint8_t)133U, (uint8_t)51U, (uint8_t)146U,
    (uint8_t)95U, (uint8_t)80U, (uint8_t)200U, (uint8_t)227U, (uint8_t)129U, (uint8_t)232U,
    (uint8_t)126U, (uint8_t)166U, (uint8_t)133U, (uint8_t)249U, (uint8_t)147U, (uint8_t)97U,
    (uint8_t)155U, (uint8_t)172U, (uint8_t)201U, (uint8_t)239U, (uint8_t)192U, (uint8_t)174U,
    (uint8_t)188U, (uint8_t)136U, (uint8_t)75U, (uint8_t)69U, (uint8_t)6U, (uint8_t)70U,
    (uint8_t)238U, (uint8_t)170U, (uint8_t)94U
  };

static uint8_t
vectors_low119[32U] =
  {
    (uint8_t)225U, (uint8_t)210U, (uint8_t)215U, (uint8_t)46U, (uint8_t)121U, (uint8_t)7U,
    (uint8_t)231U, (uint8_t)33U, (uint8_t)76U, (uint8_t)178U, (uint8_t)102U, (uint8_t)241U,
    (uint8_t)239U, (uint8_t)100U, (uint8_t)19U, (uint8_t)149U, (uint8_t)229U, (uint8_t)75U,
    (uint8_t)57U, (uint8_t)232U, (uint8_t)54U, (uint8_t)83U, (uint8_t)4U, (uint8_t)102U,
    (uint8_t)27U, (uint8_t)11U, (uint8_t)238U, (uint8_t)55U, (uint8_t)31U, (uint8_t)50U,
    (uint8_t)70U, (uint8_t)82U
  };

static uint8_t
vectors_low120[16U] =
  {
    (uint8_t)132U, (uint8_t)23U, (uint8_t)255U, (uint8_t)213U, (uint8_t)132U, (uint8_t)32U,
    (uint8_t)228U, (uint8_t)142U, (uint8_t)192U, (uint8_t)99U, (uint8_t)222U, (uint8_t)93U,
    (uint8_t)244U, (uint8_t)70U, (uint8_t)46U, (uint8_t)57U
  };

static uint8_t
vectors_low121[32U] =
  {
    (uint8_t)230U, (uint8_t)202U, (uint8_t)225U, (uint8_t)181U, (uint8_t)243U, (uint8_t)163U,
    (uint8_t)161U, (uint8_t)47U, (uint8_t)170U, (uint8_t)175U, (uint8_t)57U, (uint8_t)185U,
    (uint8_t)142U, (uint8_t)229U, (uint8_t)146U, (uint8_t)200U, (uint8_t)212U, (uint8_t)245U,
    (uint8_t)107U, (uint8_t)157U, (uint8_t)69U, (uint8_t)52U, (uint8_t)173U, (uint8_t)213U,
    (uint8_t)16U, (uint8_t)75U, (uint8_t)53U, (uint8_t)125U, (uint8_t)120U, (uint8_t)140U,
    (uint8_t)35U, (uint8_t)171U
  };

static uint8_t
vectors_low122[256U] =
  {
    (uint8_t)98U, (uint8_t)106U, (uint8_t)8U, (uint8_t)99U, (uint8_t)50U, (uint8_t)26U,
    (uint8_t)199U, (uint8_t)94U, (uint8_t)11U, (uint8_t)98U, (uint8_t)64U, (uint8_t)234U,
    (uint8_t)106U, (uint8_t)97U, (uint8_t)148U, (uint8_t)88U, (uint8_t)99U, (uint8_t)74U,
    (uint8_t)151U, (uint8_t)130U, (uint8_t)69U, (uint8_t)193U, (uint8_t)83U, (uint8_t)56U,
    (uint8_t)25U, (uint8_t)201U, (uint8_t)113U, (uint8_t)20U, (uint8_t)230U, (uint8_t)57U,
    (uint8_t)20U, (uint8_t)0U, (uint8_t)156U, (uint8_t)156U, (uint8_t)171U, (uint8_t)115U,
    (uint8_t)47U, (uint8_t)19U, (uint8_t)16U, (uint8_t)246U, (uint8_t)15U, (uint8_t)100U,
    (uint8_t)240U, (uint8_t)51U, (uint8_t)176U, (uint8_t)7U, (uint8_t)41U, (uint8_t)66U,
    (uint8_t)66U, (uint8_t)40U, (uint8_t)103U, (uint8_t)31U, (uint8_t)51U, (uint8_t)66U,
    (uint8_t)80U, (uint8_t)153U, (uint8_t)130U, (uint8_t)10U, (uint8_t)177U, (uint8_t)8U,
    (uint8_t)65U, (uint8_t)45U, (uint8_t)70U, (uint8_t)15U, (uint8_t)50U, (uint8_t)192U,
    (uint8_t)1U, (uint8_t)91U, (uint8_t)115U, (uint8_t)152U, (uint8_t)126U, (uint8_t)147U,
    (uint8_t)123U, (uint8_t)155U, (uint8_t)189U, (uint8_t)210U, (uint8_t)158U, (uint8_t)91U,
    (uint8_t)251U, (uint8_t)141U, (uint8_t)187U, (uint8_t)108U, (uint8_t)149U, (uint8_t)210U,
    (uint8_t)182U, (uint8_t)159U, (uint8_t)204U, (uint8_t)188U, (uint8_t)38U, (uint8_t)176U,
    (uint8_t)96U, (uint8_t)207U, (uint8_t)10U, (uint8_t)93U, (uint8_t)192U, (uint8_t)153U,
    (uint8_t)47U, (uint8_t)176U, (uint8_t)231U, (uint8_t)107U, (uint8_t)56U, (uint8_t)188U,
    (uint8_t)214U, (uint8_t)79U, (uint8_t)215U, (uint8_t)167U, (uint8_t)38U, (uint8_t)113U,
    (uint8_t)78U, (uint8_t)140U, (uint8_t)133U, (uint8_t)66U, (uint8_t)212U, (uint8_t)75U,
    (uint8_t)47U, (uint8_t)156U, (uint8_t)93U, (uint8_t)47U, (uint8_t)47U, (uint8_t)140U,
    (uint8_t)179U, (uint8_t)112U, (uint8_t)185U, (uint8_t)94U, (uint8_t)8U, (uint8_t)107U,
    (uint8_t)7U, (uint8_t)232U, (uint8_t)143U, (uint8_t)73U, (uint8_t)47U, (uint8_t)81U,
    (uint8_t)254U, (uint8_t)108U, (uint8_t)40U, (uint8_t)141U, (uint8_t)120U, (uint8_t)183U,
    (uint8_t)109U, (uint8_t)12U, (uint8_t)58U, (uint8_t)97U, (uint8_t)70U, (uint8_t)201U,
    (uint8_t)223U, (uint8_t)206U, (uint8_t)83U, (uint8_t)231U, (uint8_t)108U, (uint8_t)219U,
    (uint8_t)189U, (uint8_t)21U, (uint8_t)141U, (uint8_t)41U, (uint8_t)68U, (uint8_t)221U,
    (uint8_t)16U, (uint8_t)25U, (uint8_t)114U, (uint8_t)71U, (uint8_t)0U, (uint8_t)73U,
    (uint8_t)84U, (uint8_t)217U, (uint8_t)47U, (uint8_t)107U, (uint8_t)29U, (uint8_t)244U,
    (uint8_t)186U, (uint8_t)222U, (uint8_t)180U, (uint8_t)187U, (uint8_t)28U, (uint8_t)152U,
    (uint8_t)215U, (uint8_t)211U, (uint8_t)218U, (uint8_t)32U, (uint8_t)84U, (uint8_t)227U,
    (uint8_t)48U, (uint8_t)15U, (uint8_t)109U, (uint8_t)141U, (uint8_t)218U, (uint8_t)136U,
    (uint8_t)99U, (uint8_t)66U, (uint8_t)46U, (uint8_t)106U, (uint8_t)4U, (uint8_t)44U,
    (uint8_t)45U, (uint8_t)132U, (uint8_t)178U, (uint8_t)187U, (uint8_t)237U, (uint8_t)107U,
    (uint8_t)232U, (uint8_t)143U, (uint8_t)7U, (uint8_t)4U, (uint8_t)118U, (uint8_t)52U,
    (uint8_t)16U, (uint8_t)119U, (uint8_t)27U, (uint8_t)55U, (uint8_t)134U, (uint8_t)210U,
    (uint8_t)246U, (uint8_t)217U, (uint8_t)104U, (uint8_t)182U, (uint8_t)194U, (uint8_t)36U,
    (uint8_t)224U, (uint8_t)207U, (uint8_t)83U, (uint8_t)94U, (uint8_t)141U, (uint8_t)2U,
    (uint8_t)193U, (uint8_t)120U, (uint8_t)178U, (uint8_t)224U, (uint8_t)185U, (uint8_t)14U,
    (uint8_t)138U, (uint8_t)127U, (uint8_t)202U, (uint8_t)12U, (uint8_t)67U, (uint8_t)27U,
    (uint8_t)127U, (uint8_t)60U, (uint8_t)244U, (uint8_t)27U, (uint8_t)10U, (uint8_t)124U,
    (uint8_t)23U, (uint8_t)119U, (uint8_t)143U, (uint8_t)232U, (uint8_t)194U, (uint8_t)238U,
    (uint8_t)180U, (uint8_t)66U, (uint8_t)201U, (uint8_t)16U, (uint8_t)186U, (uint8_t)136U,
    (uint8_t)199U, (uint8_t)195U, (uint8_t)100U, (uint8_t)205U
  };

static uint8_t
vectors_low123[32U] =
  {
    (uint8_t)71U, (uint8_t)196U, (uint8_t)45U, (uint8_t)246U, (uint8_t)43U, (uint8_t)77U,
    (uint8_t)213U, (uint8_t)112U, (uint8_t)239U, (uint8_t)211U, (uint8_t)194U, (uint8_t)114U,
    (uint8_t)42U, (uint8_t)211U, (uint8_t)154U, (uint8_t)45U, (uint8_t)245U, (uint8_t)249U,
    (uint8_t)105U, (uint8_t)161U, (uint8_t)63U, (uint8_t)100U, (uint8_t)95U, (uint8_t)210U,
    (uint8_t)123U, (uint8_t)82U, (uint8_t)144U, (uint8_t)135U, (uint8_t)123U, (uint8_t)167U,
    (uint8_t)9U, (uint8_t)22U
  };

static uint8_t
vectors_low124[16U] =
  {
    (uint8_t)197U, (uint8_t)145U, (uint8_t)147U, (uint8_t)77U, (uint8_t)79U, (uint8_t)102U,
    (uint8_t)0U, (uint8_t)14U, (uint8_t)191U, (uint8_t)140U, (uint8_t)80U, (uint8_t)143U,
    (uint8_t)175U, (uint8_t)196U, (uint8_t)79U, (uint8_t)117U
  };

static uint8_t
vectors_low125[32U] =
  {
    (uint8_t)148U, (uint8_t)130U, (uint8_t)41U, (uint8_t)3U, (uint8_t)203U, (uint8_t)92U,
    (uint8_t)32U, (uint8_t)3U, (uint8_t)195U, (uint8_t)28U, (uint8_t)109U, (uint8_t)7U,
    (uint8_t)42U, (uint8_t)176U, (uint8_t)221U, (uint8_t)164U, (uint8_t)53U, (uint8_t)173U,
    (uint8_t)208U, (uint8_t)222U, (uint8_t)125U, (uint8_t)143U, (uint8_t)157U, (uint8_t)95U,
    (uint8_t)8U, (uint8_t)181U, (uint8_t)203U, (uint8_t)164U, (uint8_t)16U, (uint8_t)216U,
    (uint8_t)136U, (uint8_t)253U
  };

static uint8_t
vectors_low126[32U] =
  {
    (uint8_t)209U, (uint8_t)106U, (uint8_t)44U, (uint8_t)114U, (uint8_t)198U, (uint8_t)53U,
    (uint8_t)128U, (uint8_t)185U, (uint8_t)188U, (uint8_t)241U, (uint8_t)86U, (uint8_t)134U,
    (uint8_t)34U, (uint8_t)20U, (uint8_t)83U, (uint8_t)58U, (uint8_t)71U, (uint8_t)177U,
    (uint8_t)104U, (uint8_t)108U, (uint8_t)135U, (uint8_t)26U, (uint8_t)1U, (uint8_t)101U,
    (uint8_t)96U, (uint8_t)79U, (uint8_t)221U, (uint8_t)0U, (uint8_t)164U, (uint8_t)18U,
    (uint8_t)164U, (uint8_t)132U
  };

static uint8_t
vectors_low127[256U] =
  {
    (uint8_t)247U, (uint8_t)142U, (uint8_t)97U, (uint8_t)180U, (uint8_t)67U, (uint8_t)181U,
    (uint8_t)169U, (uint8_t)123U, (uint8_t)126U, (uint8_t)73U, (uint8_t)58U, (uint8_t)140U,
    (uint8_t)227U, (uint8_t)90U, (uint8_t)67U, (uint8_t)84U, (uint8_t)82U, (uint8_t)144U,
    (uint8_t)221U, (uint8_t)51U, (uint8_t)209U, (uint8_t)91U, (uint8_t)164U, (uint8_t)191U,
    (uint8_t)15U, (uint8_t)247U, (uint8_t)143U, (uint8_t)52U, (uint8_t)162U, (uint8_t)92U,
    (uint8_t)70U, (uint8_t)196U, (uint8_t)255U, (uint8_t)76U, (uint8_t)212U, (uint8_t)133U,
    (uint8_t)150U, (uint8_t)76U, (uint8_t)201U, (uint8_t)110U, (uint8_t)144U, (uint8_t)254U,
    (uint8_t)132U, (uint8_t)125U, (uint8_t)159U, (uint8_t)201U, (uint8_t)228U, (uint8_t)45U,
    (uint8_t)150U, (uint8_t)228U, (uint8_t)245U, (uint8_t)170U, (uint8_t)204U, (uint8_t)249U,
    (uint8_t)118U, (uint8_t)168U, (uint8_t)78U, (uint8_t)62U, (uint8_t)18U, (uint8_t)16U,
    (uint8_t)12U, (uint8_t)40U, (uint8_t)176U, (uint8_t)247U, (uint8_t)173U, (uint8_t)219U,
    (uint8_t)28U, (uint8_t)118U, (uint8_t)248U, (uint8_t)150U, (uint8_t)99U, (uint8_t)225U,
    (uint8_t)24U, (uint8_t)144U, (uint8_t)240U, (uint8_t)158U, (uint8_t)75U, (uint8_t)238U,
    (uint8_t)254U, (uint8_t)146U, (uint8_t)138U, (uint8_t)30U, (uint8_t)11U, (uint8_t)48U,
    (uint8_t)79U, (uint8_t)29U, (uint8_t)157U, (uint8_t)208U, (uint8_t)65U, (uint8_t)76U,
    (uint8_t)209U, (uint8_t)21U, (uint8_t)160U, (uint8_t)27U, (uint8_t)100U, (uint8_t)31U,
    (uint8_t)214U, (uint8_t)156U, (uint8_t)112U, (uint8_t)113U, (uint8_t)242U, (uint8_t)202U,
    (uint8_t)124U, (uint8_t)127U, (uint8_t)46U, (uint8_t)83U, (uint8_t)86U, (uint8_t)15U,
    (uint8_t)78U, (uint8_t)145U, (uint8_t)1U, (uint8_t)11U, (uint8_t)161U, (uint8_t)25U,
    (uint8_t)72U, (uint8_t)25U, (uint8_t)91U, (uint8_t)197U, (uint8_t)222U, (uint8_t)181U,
    (uint8_t)86U, (uint8_t)104U, (uint8_t)111U, (uint8_t)235U, (uint8_t)11U, (uint8_t)185U,
    (uint8_t)47U, (uint8_t)230U, (uint8_t)27U, (uint8_t)49U, (uint8_t)113U, (uint8_t)230U,
    (uint8_t)57U, (uint8_t)239U, (uint8_t)71U, (uint8_t)65U, (uint8_t)143U, (uint8_t)2U,
    (uint8_t)190U, (uint8_t)55U, (uint8_t)121U, (uint8_t)110U, (uint8_t)253U, (uint8_t)182U,
    (uint8_t)146U, (uint8_t)9U, (uint8_t)82U, (uint8_t)243U, (uint8_t)168U, (uint8_t)199U,
    (uint8_t)102U, (uint8_t)181U, (uint8_t)47U, (uint8_t)204U, (uint8_t)250U, (uint8_t)117U,
    (uint8_t)126U, (uint8_t)146U, (uint8_t)62U, (uint8_t)56U, (uint8_t)2U, (uint8_t)138U,
    (uint8_t)132U, (uint8_t)249U, (uint8_t)190U, (uint8_t)27U, (uint8_t)128U, (uint8_t)44U,
    (uint8_t)31U, (uint8_t)187U, (uint8_t)187U, (uint8_t)74U, (uint8_t)239U, (uint8_t)130U,
    (uint8_t)95U, (uint8_t)76U, (uint8_t)94U, (uint8_t)79U, (uint8_t)193U, (uint8_t)191U,
    (uint8_t)110U, (uint8_t)150U, (uint8_t)243U, (uint8_t)58U, (uint8_t)185U, (uint8_t)14U,
    (uint8_t)164U, (uint8_t)134U, (uint8_t)113U, (uint8_t)7U, (uint8_t)24U, (uint8_t)201U,
    (uint8_t)228U, (uint8_t)243U, (uint8_t)36U, (uint8_t)123U, (uint8_t)42U, (uint8_t)85U,
    (uint8_t)204U, (uint8_t)239U, (uint8_t)90U, (uint8_t)93U, (uint8_t)52U, (uint8_t)44U,
    (uint8_t)172U, (uint8_t)117U, (uint8_t)127U, (uint8_t)11U, (uint8_t)159U, (uint8_t)144U,
    (uint8_t)188U, (uint8_t)220U, (uint8_t)200U, (uint8_t)194U, (uint8_t)236U, (uint8_t)58U,
    (uint8_t)67U, (uint8_t)20U, (uint8_t)155U, (uint8_t)189U, (uint8_t)57U, (uint8_t)36U,
    (uint8_t)200U, (uint8_t)95U, (uint8_t)11U, (uint8_t)91U, (uint8_t)122U, (uint8_t)228U,
    (uint8_t)33U, (uint8_t)81U, (uint8_t)244U, (uint8_t)222U, (uint8_t)216U, (uint8_t)38U,
    (uint8_t)238U, (uint8_t)109U, (uint8_t)71U, (uint8_t)132U, (uint8_t)158U, (uint8_t)244U,
    (uint8_t)232U, (uint8_t)175U, (uint8_t)100U, (uint8_t)173U, (uint8_t)246U, (uint8_t)134U,
    (uint8_t)57U, (uint8_t)130U, (uint8_t)80U, (uint8_t)60U, (uint8_t)35U, (uint8_t)196U,
    (uint8_t)160U, (uint8_t)81U, (uint8_t)76U, (uint8_t)224U
  };

static uint8_t
vectors_low128[32U] =
  {
    (uint8_t)248U, (uint8_t)64U, (uint8_t)199U, (uint8_t)92U, (uint8_t)224U, (uint8_t)205U,
    (uint8_t)178U, (uint8_t)0U, (uint8_t)163U, (uint8_t)189U, (uint8_t)152U, (uint8_t)13U,
    (uint8_t)108U, (uint8_t)237U, (uint8_t)241U, (uint8_t)199U, (uint8_t)50U, (uint8_t)30U,
    (uint8_t)95U, (uint8_t)48U, (uint8_t)60U, (uint8_t)208U, (uint8_t)68U, (uint8_t)108U,
    (uint8_t)122U, (uint8_t)253U, (uint8_t)45U, (uint8_t)45U, (uint8_t)102U, (uint8_t)101U,
    (uint8_t)116U, (uint8_t)71U
  };

static uint8_t
vectors_low129[16U] =
  {
    (uint8_t)178U, (uint8_t)21U, (uint8_t)51U, (uint8_t)59U, (uint8_t)21U, (uint8_t)213U,
    (uint8_t)83U, (uint8_t)38U, (uint8_t)188U, (uint8_t)155U, (uint8_t)235U, (uint8_t)174U,
    (uint8_t)106U, (uint8_t)227U, (uint8_t)110U, (uint8_t)254U
  };

static uint8_t
vectors_low130[32U] =
  {
    (uint8_t)109U, (uint8_t)92U, (uint8_t)164U, (uint8_t)177U, (uint8_t)237U, (uint8_t)246U,
    (uint8_t)192U, (uint8_t)175U, (uint8_t)189U, (uint8_t)206U, (uint8_t)2U, (uint8_t)236U,
    (uint8_t)179U, (uint8_t)9U, (uint8_t)35U, (uint8_t)178U, (uint8_t)244U, (uint8_t)242U,
    (uint8_t)179U, (uint8_t)49U, (uint8_t)33U, (uint8_t)226U, (uint8_t)27U, (uint8_t)47U,
    (uint8_t)254U, (uint8_t)233U, (uint8_t)100U, (uint8_t)204U, (uint8_t)125U, (uint8_t)225U,
    (uint8_t)171U, (uint8_t)232U
  };

static uint8_t
vectors_low131[32U] =
  {
    (uint8_t)163U, (uint8_t)163U, (uint8_t)55U, (uint8_t)198U, (uint8_t)251U, (uint8_t)235U,
    (uint8_t)106U, (uint8_t)151U, (uint8_t)154U, (uint8_t)71U, (uint8_t)131U, (uint8_t)242U,
    (uint8_t)183U, (uint8_t)240U, (uint8_t)240U, (uint8_t)221U, (uint8_t)109U, (uint8_t)58U,
    (uint8_t)157U, (uint8_t)55U, (uint8_t)71U, (uint8_t)222U, (uint8_t)99U, (uint8_t)154U,
    (uint8_t)144U, (uint8_t)71U, (uint8_t)36U, (uint8_t)138U, (uint8_t)4U, (uint8_t)161U,
    (uint8_t)159U, (uint8_t)91U
  };

static uint8_t
vectors_low132[32U] =
  {
    (uint8_t)245U, (uint8_t)109U, (uint8_t)43U, (uint8_t)21U, (uint8_t)132U, (uint8_t)186U,
    (uint8_t)47U, (uint8_t)18U, (uint8_t)156U, (uint8_t)119U, (uint8_t)178U, (uint8_t)149U,
    (uint8_t)144U, (uint8_t)196U, (uint8_t)225U, (uint8_t)223U, (uint8_t)218U, (uint8_t)181U,
    (uint8_t)82U, (uint8_t)123U, (uint8_t)23U, (uint8_t)145U, (uint8_t)227U, (uint8_t)228U,
    (uint8_t)69U, (uint8_t)117U, (uint8_t)12U, (uint8_t)166U, (uint8_t)212U, (uint8_t)174U,
    (uint8_t)53U, (uint8_t)66U
  };

static uint8_t
vectors_low133[32U] =
  {
    (uint8_t)5U, (uint8_t)189U, (uint8_t)121U, (uint8_t)146U, (uint8_t)73U, (uint8_t)65U,
    (uint8_t)27U, (uint8_t)55U, (uint8_t)184U, (uint8_t)5U, (uint8_t)144U, (uint8_t)212U,
    (uint8_t)159U, (uint8_t)51U, (uint8_t)72U, (uint8_t)99U, (uint8_t)27U, (uint8_t)6U,
    (uint8_t)162U, (uint8_t)64U, (uint8_t)138U, (uint8_t)97U, (uint8_t)99U, (uint8_t)92U,
    (uint8_t)112U, (uint8_t)104U, (uint8_t)112U, (uint8_t)3U, (uint8_t)168U, (uint8_t)72U,
    (uint8_t)83U, (uint8_t)2U
  };

static uint8_t
vectors_low134[32U] =
  {
    (uint8_t)18U, (uint8_t)210U, (uint8_t)106U, (uint8_t)195U, (uint8_t)184U, (uint8_t)121U,
    (uint8_t)36U, (uint8_t)205U, (uint8_t)165U, (uint8_t)215U, (uint8_t)138U, (uint8_t)62U,
    (uint8_t)60U, (uint8_t)11U, (uint8_t)216U, (uint8_t)18U, (uint8_t)128U, (uint8_t)227U,
    (uint8_t)64U, (uint8_t)114U, (uint8_t)54U, (uint8_t)67U, (uint8_t)237U, (uint8_t)27U,
    (uint8_t)46U, (uint8_t)191U, (uint8_t)45U, (uint8_t)253U, (uint8_t)82U, (uint8_t)245U,
    (uint8_t)220U, (uint8_t)67U
  };

static uint8_t
vectors_low135[256U] =
  {
    (uint8_t)180U, (uint8_t)140U, (uint8_t)19U, (uint8_t)175U, (uint8_t)122U, (uint8_t)155U,
    (uint8_t)111U, (uint8_t)166U, (uint8_t)56U, (uint8_t)90U, (uint8_t)126U, (uint8_t)229U,
    (uint8_t)210U, (uint8_t)171U, (uint8_t)151U, (uint8_t)220U, (uint8_t)235U, (uint8_t)247U,
    (uint8_t)26U, (uint8_t)113U, (uint8_t)93U, (uint8_t)196U, (uint8_t)101U, (uint8_t)244U,
    (uint8_t)19U, (uint8_t)203U, (uint8_t)9U, (uint8_t)98U, (uint8_t)41U, (uint8_t)45U,
    (uint8_t)248U, (uint8_t)76U, (uint8_t)156U, (uint8_t)131U, (uint8_t)196U, (uint8_t)9U,
    (uint8_t)51U, (uint8_t)9U, (uint8_t)247U, (uint8_t)73U, (uint8_t)53U, (uint8_t)155U,
    (uint8_t)10U, (uint8_t)13U, (uint8_t)220U, (uint8_t)193U, (uint8_t)49U, (uint8_t)98U,
    (uint8_t)203U, (uint8_t)74U, (uint8_t)184U, (uint8_t)255U, (uint8_t)123U, (uint8_t)58U,
    (uint8_t)99U, (uint8_t)54U, (uint8_t)53U, (uint8_t)30U, (uint8_t)215U, (uint8_t)158U,
    (uint8_t)191U, (uint8_t)71U, (uint8_t)115U, (uint8_t)15U, (uint8_t)151U, (uint8_t)172U,
    (uint8_t)203U, (uint8_t)106U, (uint8_t)150U, (uint8_t)10U, (uint8_t)156U, (uint8_t)92U,
    (uint8_t)37U, (uint8_t)224U, (uint8_t)146U, (uint8_t)10U, (uint8_t)6U, (uint8_t)204U,
    (uint8_t)204U, (uint8_t)59U, (uint8_t)63U, (uint8_t)98U, (uint8_t)182U, (uint8_t)22U,
    (uint8_t)193U, (uint8_t)92U, (uint8_t)161U, (uint8_t)141U, (uint8_t)126U, (uint8_t)11U,
    (uint8_t)92U, (uint8_t)46U, (uint8_t)125U, (uint8_t)138U, (uint8_t)210U, (uint8_t)81U,
    (uint8_t)141U, (uint8_t)30U, (uint8_t)240U, (uint8_t)190U, (uint8_t)245U, (uint8_t)21U,
    (uint8_t)175U, (uint8_t)134U, (uint8_t)104U, (uint8_t)147U, (uint8_t)233U, (uint8_t)55U,
    (uint8_t)139U, (uint8_t)86U, (uint8_t)222U, (uint8_t)236U, (uint8_t)50U, (uint8_t)130U,
    (uint8_t)95U, (uint8_t)224U, (uint8_t)162U, (uint8_t)197U, (uint8_t)169U, (uint8_t)114U,
    (uint8_t)159U, (uint8_t)101U, (uint8_t)137U, (uint8_t)21U, (uint8_t)185U, (uint8_t)154U,
    (uint8_t)178U, (uint8_t)42U, (uint8_t)3U, (uint8_t)183U, (uint8_t)24U, (uint8_t)126U,
    (uint8_t)131U, (uint8_t)210U, (uint8_t)208U, (uint8_t)244U, (uint8_t)27U, (uint8_t)148U,
    (uint8_t)103U, (uint8_t)200U, (uint8_t)50U, (uint8_t)111U, (uint8_t)123U, (uint8_t)200U,
    (uint8_t)113U, (uint8_t)137U, (uint8_t)221U, (uint8_t)138U, (uint8_t)222U, (uint8_t)24U,
    (uint8_t)179U, (uint8_t)167U, (uint8_t)237U, (uint8_t)240U, (uint8_t)192U, (uint8_t)234U,
    (uint8_t)70U, (uint8_t)45U, (uint8_t)194U, (uint8_t)33U, (uint8_t)9U, (uint8_t)236U,
    (uint8_t)145U, (uint8_t)41U, (uint8_t)76U, (uint8_t)248U, (uint8_t)206U, (uint8_t)105U,
    (uint8_t)200U, (uint8_t)205U, (uint8_t)12U, (uint8_t)18U, (uint8_t)155U, (uint8_t)66U,
    (uint8_t)62U, (uint8_t)218U, (uint8_t)221U, (uint8_t)168U, (uint8_t)251U, (uint8_t)210U,
    (uint8_t)95U, (uint8_t)73U, (uint8_t)131U, (uint8_t)167U, (uint8_t)13U, (uint8_t)117U,
    (uint8_t)0U, (uint8_t)21U, (uint8_t)118U, (uint8_t)162U, (uint8_t)100U, (uint8_t)5U,
    (uint8_t)24U, (uint8_t)139U, (uint8_t)176U, (uint8_t)40U, (uint8_t)73U, (uint8_t)117U,
    (uint8_t)32U, (uint8_t)54U, (uint8_t)148U, (uint8_t)195U, (uint8_t)24U, (uint8_t)243U,
    (uint8_t)170U, (uint8_t)127U, (uint8_t)228U, (uint8_t)126U, (uint8_t)192U, (uint8_t)65U,
    (uint8_t)188U, (uint8_t)76U, (uint8_t)17U, (uint8_t)201U, (uint8_t)188U, (uint8_t)235U,
    (uint8_t)27U, (uint8_t)19U, (uint8_t)31U, (uint8_t)116U, (uint8_t)173U, (uint8_t)205U,
    (uint8_t)114U, (uint8_t)252U, (uint8_t)77U, (uint8_t)40U, (uint8_t)19U, (uint8_t)86U,
    (uint8_t)77U, (uint8_t)230U, (uint8_t)212U, (uint8_t)113U, (uint8_t)16U, (uint8_t)23U,
    (uint8_t)128U, (uint8_t)3U, (uint8_t)119U, (uint8_t)190U, (uint8_t)158U, (uint8_t)76U,
    (uint8_t)87U, (uint8_t)158U, (uint8_t)136U, (uint8_t)70U, (uint8_t)77U, (uint8_t)103U,
    (uint8_t)234U, (uint8_t)110U, (uint8_t)69U, (uint8_t)122U, (uint8_t)48U, (uint8_t)248U,
    (uint8_t)246U, (uint8_t)82U, (uint8_t)55U, (uint8_t)90U
  };

static uint8_t
vectors_low136[32U] =
  {
    (uint8_t)70U, (uint8_t)223U, (uint8_t)180U, (uint8_t)232U, (uint8_t)47U, (uint8_t)199U,
    (uint8_t)132U, (uint8_t)173U, (uint8_t)0U, (uint8_t)148U, (uint8_t)220U, (uint8_t)129U,
    (uint8_t)19U, (uint8_t)104U, (uint8_t)52U, (uint8_t)229U, (uint8_t)171U, (uint8_t)199U,
    (uint8_t)103U, (uint8_t)255U, (uint8_t)242U, (uint8_t)184U, (uint8_t)118U, (uint8_t)160U,
    (uint8_t)107U, (uint8_t)29U, (uint8_t)189U, (uint8_t)37U, (uint8_t)8U, (uint8_t)219U,
    (uint8_t)237U, (uint8_t)58U
  };

static uint8_t
vectors_low137[16U] =
  {
    (uint8_t)100U, (uint8_t)212U, (uint8_t)13U, (uint8_t)56U, (uint8_t)134U, (uint8_t)172U,
    (uint8_t)21U, (uint8_t)40U, (uint8_t)56U, (uint8_t)246U, (uint8_t)133U, (uint8_t)49U,
    (uint8_t)33U, (uint8_t)253U, (uint8_t)104U, (uint8_t)183U
  };

static uint8_t
vectors_low138[32U] =
  {
    (uint8_t)50U, (uint8_t)144U, (uint8_t)4U, (uint8_t)184U, (uint8_t)187U, (uint8_t)67U,
    (uint8_t)147U, (uint8_t)5U, (uint8_t)196U, (uint8_t)178U, (uint8_t)220U, (uint8_t)221U,
    (uint8_t)84U, (uint8_t)202U, (uint8_t)151U, (uint8_t)164U, (uint8_t)245U, (uint8_t)76U,
    (uint8_t)183U, (uint8_t)32U, (uint8_t)168U, (uint8_t)88U, (uint8_t)44U, (uint8_t)220U,
    (uint8_t)3U, (uint8_t)172U, (uint8_t)38U, (uint8_t)248U, (uint8_t)166U, (uint8_t)3U,
    (uint8_t)243U, (uint8_t)253U
  };

static uint8_t
vectors_low139[256U] =
  {
    (uint8_t)24U, (uint8_t)135U, (uint8_t)235U, (uint8_t)76U, (uint8_t)87U, (uint8_t)182U,
    (uint8_t)49U, (uint8_t)9U, (uint8_t)247U, (uint8_t)228U, (uint8_t)70U, (uint8_t)191U,
    (uint8_t)10U, (uint8_t)108U, (uint8_t)89U, (uint8_t)141U, (uint8_t)224U, (uint8_t)147U,
    (uint8_t)166U, (uint8_t)1U, (uint8_t)48U, (uint8_t)9U, (uint8_t)80U, (uint8_t)57U, (uint8_t)37U,
    (uint8_t)214U, (uint8_t)32U, (uint8_t)244U, (uint8_t)12U, (uint8_t)249U, (uint8_t)140U,
    (uint8_t)135U, (uint8_t)116U, (uint8_t)166U, (uint8_t)196U, (uint8_t)161U, (uint8_t)175U,
    (uint8_t)254U, (uint8_t)87U, (uint8_t)248U, (uint8_t)230U, (uint8_t)177U, (uint8_t)144U,
    (uint8_t)208U, (uint8_t)80U, (uint8_t)79U, (uint8_t)244U, (uint8_t)196U, (uint8_t)235U,
    (uint8_t)85U, (uint8_t)186U, (uint8_t)78U, (uint8_t)138U, (uint8_t)38U, (uint8_t)66U,
    (uint8_t)210U, (uint8_t)48U, (uint8_t)238U, (uint8_t)132U, (uint8_t)94U, (uint8_t)212U,
    (uint8_t)227U, (uint8_t)29U, (uint8_t)138U, (uint8_t)221U, (uint8_t)219U, (uint8_t)26U,
    (uint8_t)33U, (uint8_t)221U, (uint8_t)69U, (uint8_t)52U, (uint8_t)108U, (uint8_t)189U,
    (uint8_t)169U, (uint8_t)136U, (uint8_t)74U, (uint8_t)50U, (uint8_t)46U, (uint8_t)110U,
    (uint8_t)143U, (uint8_t)56U, (uint8_t)168U, (uint8_t)46U, (uint8_t)136U, (uint8_t)143U,
    (uint8_t)129U, (uint8_t)38U, (uint8_t)74U, (uint8_t)46U, (uint8_t)37U, (uint8_t)78U,
    (uint8_t)194U, (uint8_t)173U, (uint8_t)90U, (uint8_t)212U, (uint8_t)214U, (uint8_t)10U,
    (uint8_t)22U, (uint8_t)34U, (uint8_t)135U, (uint8_t)228U, (uint8_t)139U, (uint8_t)195U,
    (uint8_t)151U, (uint8_t)118U, (uint8_t)235U, (uint8_t)87U, (uint8_t)220U, (uint8_t)232U,
    (uint8_t)140U, (uint8_t)254U, (uint8_t)70U, (uint8_t)123U, (uint8_t)4U, (uint8_t)45U,
    (uint8_t)3U, (uint8_t)125U, (uint8_t)27U, (uint8_t)6U, (uint8_t)135U, (uint8_t)122U,
    (uint8_t)204U, (uint8_t)57U, (uint8_t)243U, (uint8_t)27U, (uint8_t)8U, (uint8_t)177U,
    (uint8_t)170U, (uint8_t)19U, (uint8_t)128U, (uint8_t)95U, (uint8_t)224U, (uint8_t)68U,
    (uint8_t)10U, (uint8_t)53U, (uint8_t)6U, (uint8_t)167U, (uint8_t)245U, (uint8_t)157U,
    (uint8_t)198U, (uint8_t)226U, (uint8_t)55U, (uint8_t)97U, (uint8_t)71U, (uint8_t)172U,
    (uint8_t)248U, (uint8_t)123U, (uint8_t)120U, (uint8_t)187U, (uint8_t)174U, (uint8_t)244U,
    (uint8_t)193U, (uint8_t)91U, (uint8_t)87U, (uint8_t)147U, (uint8_t)53U, (uint8_t)121U,
    (uint8_t)70U, (uint8_t)136U, (uint8_t)209U, (uint8_t)66U, (uint8_t)238U, (uint8_t)220U,
    (uint8_t)35U, (uint8_t)24U, (uint8_t)41U, (uint8_t)163U, (uint8_t)74U, (uint8_t)92U,
    (uint8_t)105U, (uint8_t)118U, (uint8_t)224U, (uint8_t)200U, (uint8_t)196U, (uint8_t)100U,
    (uint8_t)158U, (uint8_t)220U, (uint8_t)23U, (uint8_t)140U, (uint8_t)143U, (uint8_t)125U,
    (uint8_t)143U, (uint8_t)154U, (uint8_t)233U, (uint8_t)47U, (uint8_t)5U, (uint8_t)227U,
    (uint8_t)213U, (uint8_t)77U, (uint8_t)246U, (uint8_t)228U, (uint8_t)124U, (uint8_t)249U,
    (uint8_t)38U, (uint8_t)10U, (uint8_t)90U, (uint8_t)88U, (uint8_t)42U, (uint8_t)125U,
    (uint8_t)59U, (uint8_t)0U, (uint8_t)48U, (uint8_t)233U, (uint8_t)165U, (uint8_t)222U,
    (uint8_t)145U, (uint8_t)45U, (uint8_t)15U, (uint8_t)126U, (uint8_t)77U, (uint8_t)49U,
    (uint8_t)3U, (uint8_t)35U, (uint8_t)61U, (uint8_t)207U, (uint8_t)168U, (uint8_t)220U,
    (uint8_t)12U, (uint8_t)174U, (uint8_t)221U, (uint8_t)241U, (uint8_t)42U, (uint8_t)133U,
    (uint8_t)2U, (uint8_t)199U, (uint8_t)217U, (uint8_t)65U, (uint8_t)222U, (uint8_t)136U,
    (uint8_t)54U, (uint8_t)144U, (uint8_t)212U, (uint8_t)123U, (uint8_t)209U, (uint8_t)161U,
    (uint8_t)182U, (uint8_t)29U, (uint8_t)114U, (uint8_t)58U, (uint8_t)186U, (uint8_t)240U,
    (uint8_t)195U, (uint8_t)29U, (uint8_t)103U, (uint8_t)19U, (uint8_t)111U, (uint8_t)180U,
    (uint8_t)39U, (uint8_t)237U, (uint8_t)202U, (uint8_t)169U, (uint8_t)82U, (uint8_t)106U,
    (uint8_t)157U, (uint8_t)201U, (uint8_t)250U
  };

static uint8_t
vectors_low140[32U] =
  {
    (uint8_t)18U, (uint8_t)115U, (uint8_t)140U, (uint8_t)13U, (uint8_t)221U, (uint8_t)12U,
    (uint8_t)156U, (uint8_t)224U, (uint8_t)57U, (uint8_t)61U, (uint8_t)42U, (uint8_t)202U,
    (uint8_t)189U, (uint8_t)250U, (uint8_t)89U, (uint8_t)34U, (uint8_t)134U, (uint8_t)7U,
    (uint8_t)42U, (uint8_t)54U, (uint8_t)46U, (uint8_t)51U, (uint8_t)44U, (uint8_t)163U,
    (uint8_t)248U, (uint8_t)196U, (uint8_t)1U, (uint8_t)240U, (uint8_t)29U, (uint8_t)97U,
    (uint8_t)0U, (uint8_t)38U
  };

static uint8_t
vectors_low141[16U] =
  {
    (uint8_t)185U, (uint8_t)131U, (uint8_t)220U, (uint8_t)253U, (uint8_t)74U, (uint8_t)245U,
    (uint8_t)228U, (uint8_t)81U, (uint8_t)246U, (uint8_t)239U, (uint8_t)225U, (uint8_t)85U,
    (uint8_t)252U, (uint8_t)243U, (uint8_t)236U, (uint8_t)20U
  };

static uint8_t
vectors_low142[32U] =
  {
    (uint8_t)7U, (uint8_t)200U, (uint8_t)182U, (uint8_t)152U, (uint8_t)152U, (uint8_t)202U,
    (uint8_t)236U, (uint8_t)58U, (uint8_t)17U, (uint8_t)4U, (uint8_t)226U, (uint8_t)227U,
    (uint8_t)11U, (uint8_t)129U, (uint8_t)30U, (uint8_t)160U, (uint8_t)149U, (uint8_t)56U,
    (uint8_t)76U, (uint8_t)198U, (uint8_t)54U, (uint8_t)185U, (uint8_t)189U, (uint8_t)36U,
    (uint8_t)224U, (uint8_t)249U, (uint8_t)131U, (uint8_t)125U, (uint8_t)59U, (uint8_t)142U,
    (uint8_t)11U, (uint8_t)76U
  };

static uint8_t
vectors_low143[32U] =
  {
    (uint8_t)254U, (uint8_t)224U, (uint8_t)104U, (uint8_t)20U, (uint8_t)234U, (uint8_t)182U,
    (uint8_t)229U, (uint8_t)92U, (uint8_t)183U, (uint8_t)153U, (uint8_t)232U, (uint8_t)21U,
    (uint8_t)216U, (uint8_t)79U, (uint8_t)7U, (uint8_t)39U, (uint8_t)142U, (uint8_t)198U,
    (uint8_t)193U, (uint8_t)45U, (uint8_t)130U, (uint8_t)222U, (uint8_t)161U, (uint8_t)46U,
    (uint8_t)38U, (uint8_t)28U, (uint8_t)91U, (uint8_t)114U, (uint8_t)208U, (uint8_t)164U,
    (uint8_t)234U, (uint8_t)165U
  };

static uint8_t
vectors_low144[32U] =
  {
    (uint8_t)242U, (uint8_t)146U, (uint8_t)135U, (uint8_t)212U, (uint8_t)109U, (uint8_t)81U,
    (uint8_t)127U, (uint8_t)9U, (uint8_t)13U, (uint8_t)241U, (uint8_t)26U, (uint8_t)244U,
    (uint8_t)103U, (uint8_t)3U, (uint8_t)213U, (uint8_t)222U, (uint8_t)119U, (uint8_t)128U,
    (uint8_t)40U, (uint8_t)199U, (uint8_t)135U, (uint8_t)163U, (uint8_t)170U, (uint8_t)30U,
    (uint8_t)89U, (uint8_t)4U, (uint8_t)237U, (uint8_t)115U, (uint8_t)123U, (uint8_t)119U,
    (uint8_t)105U, (uint8_t)18U
  };

static uint8_t
vectors_low145[32U] =
  {
    (uint8_t)12U, (uint8_t)229U, (uint8_t)118U, (uint8_t)202U, (uint8_t)229U, (uint8_t)108U,
    (uint8_t)70U, (uint8_t)4U, (uint8_t)47U, (uint8_t)242U, (uint8_t)127U, (uint8_t)159U,
    (uint8_t)17U, (uint8_t)237U, (uint8_t)136U, (uint8_t)241U, (uint8_t)186U, (uint8_t)83U,
    (uint8_t)76U, (uint8_t)245U, (uint8_t)242U, (uint8_t)88U, (uint8_t)30U, (uint8_t)90U,
    (uint8_t)214U, (uint8_t)187U, (uint8_t)105U, (uint8_t)182U, (uint8_t)66U, (uint8_t)137U,
    (uint8_t)120U, (uint8_t)134U
  };

static uint8_t
vectors_low146[256U] =
  {
    (uint8_t)98U, (uint8_t)147U, (uint8_t)16U, (uint8_t)61U, (uint8_t)2U, (uint8_t)133U,
    (uint8_t)64U, (uint8_t)72U, (uint8_t)76U, (uint8_t)38U, (uint8_t)39U, (uint8_t)112U,
    (uint8_t)236U, (uint8_t)247U, (uint8_t)196U, (uint8_t)124U, (uint8_t)147U, (uint8_t)231U,
    (uint8_t)120U, (uint8_t)218U, (uint8_t)237U, (uint8_t)160U, (uint8_t)165U, (uint8_t)209U,
    (uint8_t)122U, (uint8_t)131U, (uint8_t)138U, (uint8_t)89U, (uint8_t)51U, (uint8_t)135U,
    (uint8_t)26U, (uint8_t)240U, (uint8_t)65U, (uint8_t)172U, (uint8_t)96U, (uint8_t)61U,
    (uint8_t)129U, (uint8_t)196U, (uint8_t)168U, (uint8_t)215U, (uint8_t)63U, (uint8_t)76U,
    (uint8_t)172U, (uint8_t)255U, (uint8_t)6U, (uint8_t)206U, (uint8_t)231U, (uint8_t)68U,
    (uint8_t)36U, (uint8_t)181U, (uint8_t)126U, (uint8_t)132U, (uint8_t)64U, (uint8_t)232U,
    (uint8_t)57U, (uint8_t)57U, (uint8_t)80U, (uint8_t)158U, (uint8_t)161U, (uint8_t)134U,
    (uint8_t)26U, (uint8_t)220U, (uint8_t)170U, (uint8_t)41U, (uint8_t)51U, (uint8_t)43U,
    (uint8_t)188U, (uint8_t)224U, (uint8_t)21U, (uint8_t)194U, (uint8_t)180U, (uint8_t)214U,
    (uint8_t)199U, (uint8_t)65U, (uint8_t)84U, (uint8_t)181U, (uint8_t)42U, (uint8_t)109U,
    (uint8_t)233U, (uint8_t)180U, (uint8_t)197U, (uint8_t)236U, (uint8_t)158U, (uint8_t)219U,
    (uint8_t)79U, (uint8_t)84U, (uint8_t)183U, (uint8_t)190U, (uint8_t)66U, (uint8_t)20U,
    (uint8_t)43U, (uint8_t)155U, (uint8_t)224U, (uint8_t)123U, (uint8_t)236U, (uint8_t)80U,
    (uint8_t)82U, (uint8_t)183U, (uint8_t)139U, (uint8_t)188U, (uint8_t)75U, (uint8_t)183U,
    (uint8_t)66U, (uint8_t)238U, (uint8_t)137U, (uint8_t)240U, (uint8_t)57U, (uint8_t)144U,
    (uint8_t)113U, (uint8_t)244U, (uint8_t)154U, (uint8_t)115U, (uint8_t)223U, (uint8_t)135U,
    (uint8_t)179U, (uint8_t)254U, (uint8_t)118U, (uint8_t)45U, (uint8_t)22U, (uint8_t)86U,
    (uint8_t)52U, (uint8_t)108U, (uint8_t)158U, (uint8_t)139U, (uint8_t)248U, (uint8_t)228U,
    (uint8_t)180U, (uint8_t)184U, (uint8_t)181U, (uint8_t)94U, (uint8_t)78U, (uint8_t)31U,
    (uint8_t)242U, (uint8_t)54U, (uint8_t)98U, (uint8_t)182U, (uint8_t)88U, (uint8_t)107U,
    (uint8_t)240U, (uint8_t)241U, (uint8_t)5U, (uint8_t)233U, (uint8_t)208U, (uint8_t)1U,
    (uint8_t)241U, (uint8_t)89U, (uint8_t)60U, (uint8_t)23U, (uint8_t)92U, (uint8_t)154U,
    (uint8_t)35U, (uint8_t)76U, (uint8_t)187U, (uint8_t)23U, (uint8_t)207U, (uint8_t)218U,
    (uint8_t)253U, (uint8_t)144U, (uint8_t)186U, (uint8_t)133U, (uint8_t)243U, (uint8_t)71U,
    (uint8_t)203U, (uint8_t)121U, (uint8_t)176U, (uint8_t)4U, (uint8_t)111U, (uint8_t)181U,
    (uint8_t)113U, (uint8_t)91U, (uint8_t)191U, (uint8_t)53U, (uint8_t)240U, (uint8_t)131U,
    (uint8_t)69U, (uint8_t)200U, (uint8_t)251U, (uint8_t)194U, (uint8_t)110U, (uint8_t)71U,
    (uint8_t)34U, (uint8_t)66U, (uint8_t)95U, (uint8_t)4U, (uint8_t)186U, (uint8_t)67U,
    (uint8_t)28U, (uint8_t)72U, (uint8_t)236U, (uint8_t)255U, (uint8_t)202U, (uint8_t)207U,
    (uint8_t)21U, (uint8_t)208U, (uint8_t)158U, (uint8_t)165U, (uint8_t)171U, (uint8_t)218U,
    (uint8_t)146U, (uint8_t)245U, (uint8_t)65U, (uint8_t)228U, (uint8_t)107U, (uint8_t)182U,
    (uint8_t)62U, (uint8_t)57U, (uint8_t)51U, (uint8_t)162U, (uint8_t)192U, (uint8_t)83U,
    (uint8_t)190U, (uint8_t)69U, (uint8_t)101U, (uint8_t)39U, (uint8_t)93U, (uint8_t)52U,
    (uint8_t)250U, (uint8_t)8U, (uint8_t)91U, (uint8_t)175U, (uint8_t)85U, (uint8_t)95U,
    (uint8_t)146U, (uint8_t)244U, (uint8_t)70U, (uint8_t)186U, (uint8_t)94U, (uint8_t)93U,
    (uint8_t)5U, (uint8_t)250U, (uint8_t)12U, (uint8_t)99U, (uint8_t)197U, (uint8_t)48U,
    (uint8_t)66U, (uint8_t)9U, (uint8_t)44U, (uint8_t)182U, (uint8_t)108U, (uint8_t)64U,
    (uint8_t)109U, (uint8_t)155U, (uint8_t)107U, (uint8_t)54U, (uint8_t)176U, (uint8_t)14U,
    (uint8_t)118U, (uint8_t)213U, (uint8_t)27U, (uint8_t)73U, (uint8_t)183U, (uint8_t)92U,
    (uint8_t)54U, (uint8_t)228U, (uint8_t)30U, (uint8_t)82U
  };

static uint8_t
vectors_low147[32U] =
  {
    (uint8_t)106U, (uint8_t)43U, (uint8_t)175U, (uint8_t)144U, (uint8_t)210U, (uint8_t)232U,
    (uint8_t)184U, (uint8_t)51U, (uint8_t)85U, (uint8_t)160U, (uint8_t)35U, (uint8_t)10U,
    (uint8_t)143U, (uint8_t)199U, (uint8_t)35U, (uint8_t)124U, (uint8_t)20U, (uint8_t)15U,
    (uint8_t)118U, (uint8_t)153U, (uint8_t)244U, (uint8_t)0U, (uint8_t)38U, (uint8_t)226U,
    (uint8_t)118U, (uint8_t)222U, (uint8_t)174U, (uint8_t)253U, (uint8_t)79U, (uint8_t)170U,
    (uint8_t)142U, (uint8_t)6U
  };

static uint8_t
vectors_low148[16U] =
  {
    (uint8_t)178U, (uint8_t)238U, (uint8_t)204U, (uint8_t)230U, (uint8_t)56U, (uint8_t)189U,
    (uint8_t)159U, (uint8_t)164U, (uint8_t)133U, (uint8_t)233U, (uint8_t)201U, (uint8_t)224U,
    (uint8_t)217U, (uint8_t)76U, (uint8_t)58U, (uint8_t)120U
  };

static uint8_t
vectors_low149[32U] =
  {
    (uint8_t)169U, (uint8_t)234U, (uint8_t)44U, (uint8_t)75U, (uint8_t)42U, (uint8_t)186U,
    (uint8_t)31U, (uint8_t)72U, (uint8_t)242U, (uint8_t)199U, (uint8_t)26U, (uint8_t)225U,
    (uint8_t)167U, (uint8_t)254U, (uint8_t)233U, (uint8_t)14U, (uint8_t)7U, (uint8_t)57U,
    (uint8_t)18U, (uint8_t)200U, (uint8_t)51U, (uint8_t)242U, (uint8_t)222U, (uint8_t)156U,
    (uint8_t)95U, (uint8_t)128U, (uint8_t)42U, (uint8_t)194U, (uint8_t)221U, (uint8_t)197U,
    (uint8_t)127U, (uint8_t)189U
  };

static uint8_t
vectors_low150[32U] =
  {
    (uint8_t)130U, (uint8_t)15U, (uint8_t)201U, (uint8_t)99U, (uint8_t)130U, (uint8_t)113U,
    (uint8_t)102U, (uint8_t)222U, (uint8_t)113U, (uint8_t)2U, (uint8_t)8U, (uint8_t)167U,
    (uint8_t)220U, (uint8_t)51U, (uint8_t)147U, (uint8_t)100U, (uint8_t)113U, (uint8_t)228U,
    (uint8_t)145U, (uint8_t)252U, (uint8_t)33U, (uint8_t)251U, (uint8_t)1U, (uint8_t)25U,
    (uint8_t)162U, (uint8_t)82U, (uint8_t)180U, (uint8_t)159U, (uint8_t)239U, (uint8_t)178U,
    (uint8_t)138U, (uint8_t)1U
  };

static uint8_t
vectors_low151[32U] =
  {
    (uint8_t)154U, (uint8_t)70U, (uint8_t)52U, (uint8_t)132U, (uint8_t)209U, (uint8_t)114U,
    (uint8_t)16U, (uint8_t)136U, (uint8_t)7U, (uint8_t)196U, (uint8_t)60U, (uint8_t)4U,
    (uint8_t)139U, (uint8_t)209U, (uint8_t)58U, (uint8_t)114U, (uint8_t)209U, (uint8_t)91U,
    (uint8_t)71U, (uint8_t)12U, (uint8_t)52U, (uint8_t)67U, (uint8_t)57U, (uint8_t)7U,
    (uint8_t)116U, (uint8_t)165U, (uint8_t)85U, (uint8_t)114U, (uint8_t)208U, (uint8_t)63U,
    (uint8_t)71U, (uint8_t)177U
  };

static uint8_t
vectors_low152[32U] =
  {
    (uint8_t)217U, (uint8_t)134U, (uint8_t)113U, (uint8_t)151U, (uint8_t)138U, (uint8_t)225U,
    (uint8_t)75U, (uint8_t)53U, (uint8_t)49U, (uint8_t)57U, (uint8_t)74U, (uint8_t)7U,
    (uint8_t)133U, (uint8_t)247U, (uint8_t)130U, (uint8_t)66U, (uint8_t)212U, (uint8_t)179U,
    (uint8_t)46U, (uint8_t)182U, (uint8_t)28U, (uint8_t)255U, (uint8_t)236U, (uint8_t)96U,
    (uint8_t)136U, (uint8_t)239U, (uint8_t)184U, (uint8_t)98U, (uint8_t)86U, (uint8_t)147U,
    (uint8_t)39U, (uint8_t)106U
  };

static uint8_t
vectors_low153[32U] =
  {
    (uint8_t)185U, (uint8_t)174U, (uint8_t)243U, (uint8_t)44U, (uint8_t)64U, (uint8_t)183U,
    (uint8_t)170U, (uint8_t)79U, (uint8_t)215U, (uint8_t)50U, (uint8_t)228U, (uint8_t)67U,
    (uint8_t)27U, (uint8_t)237U, (uint8_t)206U, (uint8_t)7U, (uint8_t)30U, (uint8_t)79U,
    (uint8_t)100U, (uint8_t)64U, (uint8_t)91U, (uint8_t)225U, (uint8_t)200U, (uint8_t)93U,
    (uint8_t)224U, (uint8_t)60U, (uint8_t)127U, (uint8_t)170U, (uint8_t)10U, (uint8_t)167U,
    (uint8_t)39U, (uint8_t)15U
  };

static uint8_t
vectors_low154[256U] =
  {
    (uint8_t)245U, (uint8_t)87U, (uint8_t)145U, (uint8_t)253U, (uint8_t)201U, (uint8_t)215U,
    (uint8_t)99U, (uint8_t)195U, (uint8_t)76U, (uint8_t)15U, (uint8_t)196U, (uint8_t)204U,
    (uint8_t)69U, (uint8_t)122U, (uint8_t)67U, (uint8_t)132U, (uint8_t)150U, (uint8_t)241U,
    (uint8_t)143U, (uint8_t)72U, (uint8_t)60U, (uint8_t)198U, (uint8_t)12U, (uint8_t)73U,
    (uint8_t)63U, (uint8_t)205U, (uint8_t)5U, (uint8_t)73U, (uint8_t)129U, (uint8_t)47U,
    (uint8_t)173U, (uint8_t)121U, (uint8_t)47U, (uint8_t)146U, (uint8_t)56U, (uint8_t)21U,
    (uint8_t)50U, (uint8_t)84U, (uint8_t)138U, (uint8_t)140U, (uint8_t)34U, (uint8_t)87U,
    (uint8_t)198U, (uint8_t)228U, (uint8_t)36U, (uint8_t)250U, (uint8_t)87U, (uint8_t)10U,
    (uint8_t)242U, (uint8_t)96U, (uint8_t)189U, (uint8_t)71U, (uint8_t)222U, (uint8_t)146U,
    (uint8_t)242U, (uint8_t)72U, (uint8_t)245U, (uint8_t)114U, (uint8_t)145U, (uint8_t)254U,
    (uint8_t)173U, (uint8_t)58U, (uint8_t)104U, (uint8_t)201U, (uint8_t)75U, (uint8_t)233U,
    (uint8_t)220U, (uint8_t)18U, (uint8_t)166U, (uint8_t)86U, (uint8_t)99U, (uint8_t)6U,
    (uint8_t)34U, (uint8_t)190U, (uint8_t)155U, (uint8_t)96U, (uint8_t)45U, (uint8_t)79U,
    (uint8_t)197U, (uint8_t)3U, (uint8_t)124U, (uint8_t)41U, (uint8_t)187U, (uint8_t)181U,
    (uint8_t)250U, (uint8_t)146U, (uint8_t)254U, (uint8_t)210U, (uint8_t)35U, (uint8_t)81U,
    (uint8_t)134U, (uint8_t)4U, (uint8_t)143U, (uint8_t)101U, (uint8_t)33U, (uint8_t)49U,
    (uint8_t)248U, (uint8_t)69U, (uint8_t)240U, (uint8_t)30U, (uint8_t)215U, (uint8_t)24U,
    (uint8_t)186U, (uint8_t)240U, (uint8_t)89U, (uint8_t)87U, (uint8_t)232U, (uint8_t)99U,
    (uint8_t)35U, (uint8_t)158U, (uint8_t)148U, (uint8_t)165U, (uint8_t)97U, (uint8_t)58U,
    (uint8_t)164U, (uint8_t)125U, (uint8_t)210U, (uint8_t)93U, (uint8_t)91U, (uint8_t)201U,
    (uint8_t)241U, (uint8_t)112U, (uint8_t)228U, (uint8_t)4U, (uint8_t)126U, (uint8_t)134U,
    (uint8_t)239U, (uint8_t)30U, (uint8_t)239U, (uint8_t)166U, (uint8_t)14U, (uint8_t)53U,
    (uint8_t)159U, (uint8_t)34U, (uint8_t)4U, (uint8_t)163U, (uint8_t)244U, (uint8_t)83U,
    (uint8_t)201U, (uint8_t)179U, (uint8_t)125U, (uint8_t)207U, (uint8_t)217U, (uint8_t)65U,
    (uint8_t)7U, (uint8_t)54U, (uint8_t)238U, (uint8_t)20U, (uint8_t)226U, (uint8_t)150U,
    (uint8_t)171U, (uint8_t)205U, (uint8_t)193U, (uint8_t)133U, (uint8_t)243U, (uint8_t)237U,
    (uint8_t)49U, (uint8_t)216U, (uint8_t)173U, (uint8_t)70U, (uint8_t)26U, (uint8_t)129U,
    (uint8_t)71U, (uint8_t)159U, (uint8_t)149U, (uint8_t)126U, (uint8_t)105U, (uint8_t)195U,
    (uint8_t)67U, (uint8_t)52U, (uint8_t)162U, (uint8_t)78U, (uint8_t)34U, (uint8_t)244U,
    (uint8_t)166U, (uint8_t)150U, (uint8_t)6U, (uint8_t)219U, (uint8_t)139U, (uint8_t)202U,
    (uint8_t)108U, (uint8_t)177U, (uint8_t)137U, (uint8_t)231U, (uint8_t)222U, (uint8_t)75U,
    (uint8_t)131U, (uint8_t)216U, (uint8_t)161U, (uint8_t)4U, (uint8_t)97U, (uint8_t)251U,
    (uint8_t)161U, (uint8_t)148U, (uint8_t)44U, (uint8_t)131U, (uint8_t)170U, (uint8_t)46U,
    (uint8_t)95U, (uint8_t)132U, (uint8_t)220U, (uint8_t)237U, (uint8_t)148U, (uint8_t)64U,
    (uint8_t)241U, (uint8_t)10U, (uint8_t)84U, (uint8_t)199U, (uint8_t)65U, (uint8_t)83U,
    (uint8_t)100U, (uint8_t)50U, (uint8_t)135U, (uint8_t)49U, (uint8_t)58U, (uint8_t)231U,
    (uint8_t)254U, (uint8_t)27U, (uint8_t)242U, (uint8_t)60U, (uint8_t)106U, (uint8_t)190U,
    (uint8_t)204U, (uint8_t)85U, (uint8_t)196U, (uint8_t)163U, (uint8_t)245U, (uint8_t)84U,
    (uint8_t)4U, (uint8_t)149U, (uint8_t)183U, (uint8_t)210U, (uint8_t)154U, (uint8_t)48U,
    (uint8_t)45U, (uint8_t)66U, (uint8_t)110U, (uint8_t)226U, (uint8_t)241U, (uint8_t)61U,
    (uint8_t)217U, (uint8_t)237U, (uint8_t)122U, (uint8_t)90U, (uint8_t)102U, (uint8_t)24U,
    (uint8_t)114U, (uint8_t)69U, (uint8_t)68U, (uint8_t)218U, (uint8_t)99U, (uint8_t)82U,
    (uint8_t)124U, (uint8_t)112U, (uint8_t)46U, (uint8_t)76U
  };

static uint8_t
vectors_low155[32U] =
  {
    (uint8_t)71U, (uint8_t)19U, (uint8_t)159U, (uint8_t)84U, (uint8_t)74U, (uint8_t)249U,
    (uint8_t)246U, (uint8_t)176U, (uint8_t)184U, (uint8_t)2U, (uint8_t)43U, (uint8_t)186U,
    (uint8_t)229U, (uint8_t)185U, (uint8_t)54U, (uint8_t)163U, (uint8_t)244U, (uint8_t)191U,
    (uint8_t)138U, (uint8_t)15U, (uint8_t)28U, (uint8_t)209U, (uint8_t)12U, (uint8_t)140U,
    (uint8_t)95U, (uint8_t)184U, (uint8_t)187U, (uint8_t)115U, (uint8_t)99U, (uint8_t)223U,
    (uint8_t)100U, (uint8_t)17U
  };

static uint8_t
vectors_low156[16U] =
  {
    (uint8_t)185U, (uint8_t)150U, (uint8_t)64U, (uint8_t)247U, (uint8_t)12U, (uint8_t)123U,
    (uint8_t)85U, (uint8_t)96U, (uint8_t)95U, (uint8_t)123U, (uint8_t)238U, (uint8_t)103U,
    (uint8_t)83U, (uint8_t)243U, (uint8_t)6U, (uint8_t)117U
  };

static uint8_t
vectors_low157[32U] =
  {
    (uint8_t)15U, (uint8_t)136U, (uint8_t)53U, (uint8_t)117U, (uint8_t)25U, (uint8_t)232U,
    (uint8_t)242U, (uint8_t)192U, (uint8_t)84U, (uint8_t)149U, (uint8_t)197U, (uint8_t)149U,
    (uint8_t)5U, (uint8_t)110U, (uint8_t)96U, (uint8_t)35U, (uint8_t)70U, (uint8_t)11U,
    (uint8_t)234U, (uint8_t)71U, (uint8_t)231U, (uint8_t)159U, (uint8_t)114U, (uint8_t)177U,
    (uint8_t)19U, (uint8_t)120U, (uint8_t)78U, (uint8_t)182U, (uint8_t)167U, (uint8_t)127U,
    (uint8_t)159U, (uint8_t)40U
  };

static uint8_t
vectors_low158[32U] =
  {
    (uint8_t)131U, (uint8_t)237U, (uint8_t)127U, (uint8_t)181U, (uint8_t)174U, (uint8_t)133U,
    (uint8_t)19U, (uint8_t)129U, (uint8_t)97U, (uint8_t)254U, (uint8_t)144U, (uint8_t)177U,
    (uint8_t)75U, (uint8_t)21U, (uint8_t)41U, (uint8_t)91U, (uint8_t)17U, (uint8_t)216U,
    (uint8_t)27U, (uint8_t)14U, (uint8_t)203U, (uint8_t)217U, (uint8_t)241U, (uint8_t)131U,
    (uint8_t)138U, (uint8_t)40U, (uint8_t)88U, (uint8_t)207U, (uint8_t)158U, (uint8_t)130U,
    (uint8_t)40U, (uint8_t)134U
  };

static uint8_t
vectors_low159[32U] =
  {
    (uint8_t)233U, (uint8_t)115U, (uint8_t)234U, (uint8_t)45U, (uint8_t)57U, (uint8_t)155U,
    (uint8_t)156U, (uint8_t)74U, (uint8_t)214U, (uint8_t)133U, (uint8_t)65U, (uint8_t)26U,
    (uint8_t)97U, (uint8_t)155U, (uint8_t)122U, (uint8_t)92U, (uint8_t)230U, (uint8_t)246U,
    (uint8_t)86U, (uint8_t)139U, (uint8_t)198U, (uint8_t)110U, (uint8_t)251U, (uint8_t)136U,
    (uint8_t)85U, (uint8_t)166U, (uint8_t)159U, (uint8_t)37U, (uint8_t)104U, (uint8_t)41U,
    (uint8_t)166U, (uint8_t)45U
  };

static uint8_t
vectors_low160[32U] =
  {
    (uint8_t)27U, (uint8_t)216U, (uint8_t)9U, (uint8_t)1U, (uint8_t)4U, (uint8_t)183U,
    (uint8_t)136U, (uint8_t)68U, (uint8_t)246U, (uint8_t)214U, (uint8_t)21U, (uint8_t)233U,
    (uint8_t)59U, (uint8_t)122U, (uint8_t)224U, (uint8_t)201U, (uint8_t)33U, (uint8_t)81U,
    (uint8_t)124U, (uint8_t)151U, (uint8_t)115U, (uint8_t)92U, (uint8_t)10U, (uint8_t)170U,
    (uint8_t)40U, (uint8_t)205U, (uint8_t)238U, (uint8_t)30U, (uint8_t)176U, (uint8_t)161U,
    (uint8_t)70U, (uint8_t)89U
  };

static uint8_t
vectors_low161[32U] =
  {
    (uint8_t)77U, (uint8_t)87U, (uint8_t)208U, (uint8_t)79U, (uint8_t)192U, (uint8_t)162U,
    (uint8_t)173U, (uint8_t)198U, (uint8_t)235U, (uint8_t)182U, (uint8_t)24U, (uint8_t)241U,
    (uint8_t)35U, (uint8_t)111U, (uint8_t)238U, (uint8_t)14U, (uint8_t)176U, (uint8_t)14U,
    (uint8_t)56U, (uint8_t)255U, (uint8_t)130U, (uint8_t)19U, (uint8_t)127U, (uint8_t)94U,
    (uint8_t)55U, (uint8_t)91U, (uint8_t)224U, (uint8_t)10U, (uint8_t)209U, (uint8_t)170U,
    (uint8_t)195U, (uint8_t)94U
  };

static uint8_t
vectors_low162[256U] =
  {
    (uint8_t)140U, (uint8_t)76U, (uint8_t)227U, (uint8_t)41U, (uint8_t)42U, (uint8_t)229U,
    (uint8_t)0U, (uint8_t)85U, (uint8_t)123U, (uint8_t)64U, (uint8_t)228U, (uint8_t)33U,
    (uint8_t)86U, (uint8_t)101U, (uint8_t)200U, (uint8_t)219U, (uint8_t)92U, (uint8_t)203U,
    (uint8_t)161U, (uint8_t)63U, (uint8_t)189U, (uint8_t)45U, (uint8_t)38U, (uint8_t)202U,
    (uint8_t)141U, (uint8_t)31U, (uint8_t)218U, (uint8_t)217U, (uint8_t)220U, (uint8_t)161U,
    (uint8_t)88U, (uint8_t)55U, (uint8_t)30U, (uint8_t)192U, (uint8_t)0U, (uint8_t)60U,
    (uint8_t)248U, (uint8_t)1U, (uint8_t)253U, (uint8_t)40U, (uint8_t)116U, (uint8_t)26U,
    (uint8_t)47U, (uint8_t)211U, (uint8_t)29U, (uint8_t)21U, (uint8_t)228U, (uint8_t)192U,
    (uint8_t)97U, (uint8_t)44U, (uint8_t)104U, (uint8_t)225U, (uint8_t)159U, (uint8_t)164U,
    (uint8_t)225U, (uint8_t)156U, (uint8_t)98U, (uint8_t)108U, (uint8_t)228U, (uint8_t)176U,
    (uint8_t)24U, (uint8_t)67U, (uint8_t)3U, (uint8_t)244U, (uint8_t)84U, (uint8_t)76U,
    (uint8_t)65U, (uint8_t)74U, (uint8_t)101U, (uint8_t)65U, (uint8_t)199U, (uint8_t)212U,
    (uint8_t)172U, (uint8_t)94U, (uint8_t)101U, (uint8_t)85U, (uint8_t)210U, (uint8_t)46U,
    (uint8_t)33U, (uint8_t)192U, (uint8_t)154U, (uint8_t)9U, (uint8_t)106U, (uint8_t)169U,
    (uint8_t)236U, (uint8_t)9U, (uint8_t)201U, (uint8_t)2U, (uint8_t)235U, (uint8_t)103U,
    (uint8_t)162U, (uint8_t)222U, (uint8_t)158U, (uint8_t)186U, (uint8_t)148U, (uint8_t)183U,
    (uint8_t)25U, (uint8_t)236U, (uint8_t)27U, (uint8_t)164U, (uint8_t)221U, (uint8_t)93U,
    (uint8_t)186U, (uint8_t)254U, (uint8_t)233U, (uint8_t)63U, (uint8_t)205U, (uint8_t)81U,
    (uint8_t)37U, (uint8_t)34U, (uint8_t)62U, (uint8_t)170U, (uint8_t)224U, (uint8_t)191U,
    (uint8_t)13U, (uint8_t)142U, (uint8_t)126U, (uint8_t)185U, (uint8_t)46U, (uint8_t)160U,
    (uint8_t)97U, (uint8_t)12U, (uint8_t)195U, (uint8_t)43U, (uint8_t)105U, (uint8_t)88U,
    (uint8_t)76U, (uint8_t)10U, (uint8_t)21U, (uint8_t)101U, (uint8_t)128U, (uint8_t)32U,
    (uint8_t)40U, (uint8_t)243U, (uint8_t)30U, (uint8_t)105U, (uint8_t)16U, (uint8_t)2U,
    (uint8_t)29U, (uint8_t)97U, (uint8_t)142U, (uint8_t)81U, (uint8_t)56U, (uint8_t)19U,
    (uint8_t)126U, (uint8_t)204U, (uint8_t)171U, (uint8_t)137U, (uint8_t)74U, (uint8_t)83U,
    (uint8_t)133U, (uint8_t)202U, (uint8_t)69U, (uint8_t)68U, (uint8_t)253U, (uint8_t)242U,
    (uint8_t)9U, (uint8_t)25U, (uint8_t)239U, (uint8_t)34U, (uint8_t)22U, (uint8_t)163U,
    (uint8_t)234U, (uint8_t)244U, (uint8_t)79U, (uint8_t)218U, (uint8_t)204U, (uint8_t)127U,
    (uint8_t)224U, (uint8_t)92U, (uint8_t)226U, (uint8_t)46U, (uint8_t)86U, (uint8_t)90U,
    (uint8_t)90U, (uint8_t)176U, (uint8_t)19U, (uint8_t)205U, (uint8_t)108U, (uint8_t)158U,
    (uint8_t)10U, (uint8_t)128U, (uint8_t)180U, (uint8_t)48U, (uint8_t)250U, (uint8_t)139U,
    (uint8_t)114U, (uint8_t)18U, (uint8_t)127U, (uint8_t)132U, (uint8_t)243U, (uint8_t)167U,
    (uint8_t)128U, (uint8_t)212U, (uint8_t)238U, (uint8_t)146U, (uint8_t)199U, (uint8_t)41U,
    (uint8_t)1U, (uint8_t)234U, (uint8_t)252U, (uint8_t)138U, (uint8_t)33U, (uint8_t)197U,
    (uint8_t)109U, (uint8_t)204U, (uint8_t)104U, (uint8_t)122U, (uint8_t)196U, (uint8_t)206U,
    (uint8_t)70U, (uint8_t)76U, (uint8_t)206U, (uint8_t)6U, (uint8_t)136U, (uint8_t)149U,
    (uint8_t)71U, (uint8_t)27U, (uint8_t)54U, (uint8_t)247U, (uint8_t)181U, (uint8_t)137U,
    (uint8_t)135U, (uint8_t)174U, (uint8_t)50U, (uint8_t)114U, (uint8_t)88U, (uint8_t)31U,
    (uint8_t)0U, (uint8_t)248U, (uint8_t)214U, (uint8_t)103U, (uint8_t)8U, (uint8_t)91U,
    (uint8_t)222U, (uint8_t)173U, (uint8_t)203U, (uint8_t)6U, (uint8_t)255U, (uint8_t)239U,
    (uint8_t)91U, (uint8_t)27U, (uint8_t)50U, (uint8_t)155U, (uint8_t)241U, (uint8_t)219U,
    (uint8_t)113U, (uint8_t)206U, (uint8_t)16U, (uint8_t)26U, (uint8_t)45U, (uint8_t)105U,
    (uint8_t)77U, (uint8_t)233U, (uint8_t)227U, (uint8_t)34U
  };

static uint8_t
vectors_low163[32U] =
  {
    (uint8_t)40U, (uint8_t)134U, (uint8_t)255U, (uint8_t)78U, (uint8_t)17U, (uint8_t)149U,
    (uint8_t)12U, (uint8_t)30U, (uint8_t)99U, (uint8_t)147U, (uint8_t)152U, (uint8_t)178U,
    (uint8_t)199U, (uint8_t)214U, (uint8_t)144U, (uint8_t)141U, (uint8_t)92U, (uint8_t)46U,
    (uint8_t)77U, (uint8_t)174U, (uint8_t)183U, (uint8_t)113U, (uint8_t)158U, (uint8_t)109U,
    (uint8_t)217U, (uint8_t)138U, (uint8_t)57U, (uint8_t)177U, (uint8_t)66U, (uint8_t)142U,
    (uint8_t)167U, (uint8_t)223U
  };

static uint8_t
vectors_low164[16U] =
  {
    (uint8_t)140U, (uint8_t)187U, (uint8_t)151U, (uint8_t)245U, (uint8_t)140U, (uint8_t)242U,
    (uint8_t)67U, (uint8_t)4U, (uint8_t)91U, (uint8_t)218U, (uint8_t)219U, (uint8_t)47U,
    (uint8_t)155U, (uint8_t)189U, (uint8_t)171U, (uint8_t)16U
  };

static uint8_t
vectors_low165[32U] =
  {
    (uint8_t)244U, (uint8_t)135U, (uint8_t)185U, (uint8_t)75U, (uint8_t)94U, (uint8_t)78U,
    (uint8_t)218U, (uint8_t)73U, (uint8_t)233U, (uint8_t)51U, (uint8_t)224U, (uint8_t)194U,
    (uint8_t)104U, (uint8_t)235U, (uint8_t)80U, (uint8_t)66U, (uint8_t)196U, (uint8_t)34U,
    (uint8_t)223U, (uint8_t)136U, (uint8_t)6U, (uint8_t)30U, (uint8_t)191U, (uint8_t)253U,
    (uint8_t)137U, (uint8_t)61U, (uint8_t)57U, (uint8_t)250U, (uint8_t)253U, (uint8_t)88U,
    (uint8_t)239U, (uint8_t)211U
  };

static uint8_t
vectors_low166[32U] =
  {
    (uint8_t)255U, (uint8_t)142U, (uint8_t)118U, (uint8_t)86U, (uint8_t)162U, (uint8_t)27U,
    (uint8_t)204U, (uint8_t)237U, (uint8_t)8U, (uint8_t)41U, (uint8_t)114U, (uint8_t)113U,
    (uint8_t)158U, (uint8_t)191U, (uint8_t)135U, (uint8_t)83U, (uint8_t)156U, (uint8_t)72U,
    (uint8_t)37U, (uint8_t)203U, (uint8_t)15U, (uint8_t)75U, (uint8_t)234U, (uint8_t)189U,
    (uint8_t)18U, (uint8_t)161U, (uint8_t)45U, (uint8_t)84U, (uint8_t)77U, (uint8_t)234U,
    (uint8_t)135U, (uint8_t)175U
  };

static uint8_t
vectors_low167[32U] =
  {
    (uint8_t)246U, (uint8_t)77U, (uint8_t)211U, (uint8_t)176U, (uint8_t)239U, (uint8_t)197U,
    (uint8_t)200U, (uint8_t)193U, (uint8_t)70U, (uint8_t)249U, (uint8_t)185U, (uint8_t)184U,
    (uint8_t)240U, (uint8_t)236U, (uint8_t)124U, (uint8_t)203U, (uint8_t)120U, (uint8_t)78U,
    (uint8_t)135U, (uint8_t)193U, (uint8_t)98U, (uint8_t)104U, (uint8_t)164U, (uint8_t)170U,
    (uint8_t)179U, (uint8_t)30U, (uint8_t)158U, (uint8_t)221U, (uint8_t)242U, (uint8_t)201U,
    (uint8_t)184U, (uint8_t)62U
  };

static uint8_t
vectors_low168[32U] =
  {
    (uint8_t)157U, (uint8_t)193U, (uint8_t)107U, (uint8_t)149U, (uint8_t)90U, (uint8_t)232U,
    (uint8_t)5U, (uint8_t)241U, (uint8_t)14U, (uint8_t)187U, (uint8_t)220U, (uint8_t)55U,
    (uint8_t)148U, (uint8_t)162U, (uint8_t)171U, (uint8_t)230U, (uint8_t)113U, (uint8_t)163U,
    (uint8_t)57U, (uint8_t)202U, (uint8_t)20U, (uint8_t)139U, (uint8_t)70U, (uint8_t)239U,
    (uint8_t)110U, (uint8_t)162U, (uint8_t)8U, (uint8_t)105U, (uint8_t)138U, (uint8_t)84U,
    (uint8_t)160U, (uint8_t)216U
  };

static uint8_t
vectors_low169[256U] =
  {
    (uint8_t)14U, (uint8_t)140U, (uint8_t)156U, (uint8_t)185U, (uint8_t)159U, (uint8_t)236U,
    (uint8_t)55U, (uint8_t)96U, (uint8_t)43U, (uint8_t)41U, (uint8_t)30U, (uint8_t)80U,
    (uint8_t)142U, (uint8_t)67U, (uint8_t)194U, (uint8_t)171U, (uint8_t)50U, (uint8_t)61U,
    (uint8_t)5U, (uint8_t)118U, (uint8_t)65U, (uint8_t)132U, (uint8_t)55U, (uint8_t)156U,
    (uint8_t)163U, (uint8_t)162U, (uint8_t)202U, (uint8_t)64U, (uint8_t)128U, (uint8_t)237U,
    (uint8_t)38U, (uint8_t)194U, (uint8_t)219U, (uint8_t)253U, (uint8_t)243U, (uint8_t)209U,
    (uint8_t)145U, (uint8_t)100U, (uint8_t)133U, (uint8_t)199U, (uint8_t)235U, (uint8_t)164U,
    (uint8_t)144U, (uint8_t)119U, (uint8_t)202U, (uint8_t)136U, (uint8_t)31U, (uint8_t)176U,
    (uint8_t)61U, (uint8_t)7U, (uint8_t)249U, (uint8_t)103U, (uint8_t)202U, (uint8_t)217U,
    (uint8_t)180U, (uint8_t)119U, (uint8_t)149U, (uint8_t)159U, (uint8_t)0U, (uint8_t)122U,
    (uint8_t)97U, (uint8_t)136U, (uint8_t)21U, (uint8_t)11U, (uint8_t)102U, (uint8_t)48U,
    (uint8_t)33U, (uint8_t)138U, (uint8_t)245U, (uint8_t)95U, (uint8_t)221U, (uint8_t)123U,
    (uint8_t)226U, (uint8_t)235U, (uint8_t)136U, (uint8_t)212U, (uint8_t)139U, (uint8_t)94U,
    (uint8_t)198U, (uint8_t)182U, (uint8_t)135U, (uint8_t)110U, (uint8_t)194U, (uint8_t)86U,
    (uint8_t)101U, (uint8_t)192U, (uint8_t)49U, (uint8_t)6U, (uint8_t)36U, (uint8_t)40U,
    (uint8_t)61U, (uint8_t)43U, (uint8_t)84U, (uint8_t)96U, (uint8_t)227U, (uint8_t)115U,
    (uint8_t)111U, (uint8_t)139U, (uint8_t)159U, (uint8_t)11U, (uint8_t)132U, (uint8_t)9U,
    (uint8_t)90U, (uint8_t)164U, (uint8_t)117U, (uint8_t)74U, (uint8_t)197U, (uint8_t)144U,
    (uint8_t)103U, (uint8_t)167U, (uint8_t)204U, (uint8_t)115U, (uint8_t)64U, (uint8_t)44U,
    (uint8_t)9U, (uint8_t)177U, (uint8_t)118U, (uint8_t)137U, (uint8_t)114U, (uint8_t)179U,
    (uint8_t)171U, (uint8_t)212U, (uint8_t)158U, (uint8_t)14U, (uint8_t)35U, (uint8_t)122U,
    (uint8_t)116U, (uint8_t)22U, (uint8_t)73U, (uint8_t)234U, (uint8_t)120U, (uint8_t)136U,
    (uint8_t)234U, (uint8_t)74U, (uint8_t)2U, (uint8_t)76U, (uint8_t)9U, (uint8_t)82U,
    (uint8_t)185U, (uint8_t)74U, (uint8_t)242U, (uint8_t)124U, (uint8_t)83U, (uint8_t)177U,
    (uint8_t)58U, (uint8_t)252U, (uint8_t)170U, (uint8_t)79U, (uint8_t)183U, (uint8_t)151U,
    (uint8_t)111U, (uint8_t)101U, (uint8_t)68U, (uint8_t)56U, (uint8_t)9U, (uint8_t)209U,
    (uint8_t)187U, (uint8_t)215U, (uint8_t)228U, (uint8_t)183U, (uint8_t)65U, (uint8_t)188U,
    (uint8_t)214U, (uint8_t)196U, (uint8_t)163U, (uint8_t)242U, (uint8_t)205U, (uint8_t)248U,
    (uint8_t)99U, (uint8_t)231U, (uint8_t)25U, (uint8_t)229U, (uint8_t)213U, (uint8_t)230U,
    (uint8_t)0U, (uint8_t)67U, (uint8_t)231U, (uint8_t)113U, (uint8_t)206U, (uint8_t)83U,
    (uint8_t)85U, (uint8_t)222U, (uint8_t)225U, (uint8_t)197U, (uint8_t)41U, (uint8_t)157U,
    (uint8_t)223U, (uint8_t)165U, (uint8_t)77U, (uint8_t)119U, (uint8_t)221U, (uint8_t)222U,
    (uint8_t)41U, (uint8_t)36U, (uint8_t)39U, (uint8_t)28U, (uint8_t)14U, (uint8_t)206U,
    (uint8_t)30U, (uint8_t)30U, (uint8_t)30U, (uint8_t)138U, (uint8_t)166U, (uint8_t)33U,
    (uint8_t)140U, (uint8_t)8U, (uint8_t)174U, (uint8_t)228U, (uint8_t)9U, (uint8_t)147U,
    (uint8_t)238U, (uint8_t)213U, (uint8_t)137U, (uint8_t)89U, (uint8_t)175U, (uint8_t)67U,
    (uint8_t)12U, (uint8_t)125U, (uint8_t)83U, (uint8_t)180U, (uint8_t)23U, (uint8_t)154U,
    (uint8_t)163U, (uint8_t)85U, (uint8_t)254U, (uint8_t)188U, (uint8_t)196U, (uint8_t)1U,
    (uint8_t)36U, (uint8_t)203U, (uint8_t)122U, (uint8_t)29U, (uint8_t)41U, (uint8_t)101U,
    (uint8_t)227U, (uint8_t)104U, (uint8_t)50U, (uint8_t)229U, (uint8_t)244U, (uint8_t)47U,
    (uint8_t)154U, (uint8_t)72U, (uint8_t)39U, (uint8_t)88U, (uint8_t)136U, (uint8_t)114U,
    (uint8_t)92U, (uint8_t)186U, (uint8_t)40U, (uint8_t)215U, (uint8_t)35U, (uint8_t)152U,
    (uint8_t)251U, (uint8_t)239U, (uint8_t)172U, (uint8_t)148U
  };

static uint8_t
vectors_low170[32U] =
  {
    (uint8_t)40U, (uint8_t)134U, (uint8_t)255U, (uint8_t)78U, (uint8_t)17U, (uint8_t)149U,
    (uint8_t)12U, (uint8_t)30U, (uint8_t)99U, (uint8_t)147U, (uint8_t)152U, (uint8_t)178U,
    (uint8_t)199U, (uint8_t)214U, (uint8_t)144U, (uint8_t)141U, (uint8_t)92U, (uint8_t)46U,
    (uint8_t)77U, (uint8_t)174U, (uint8_t)183U, (uint8_t)113U, (uint8_t)158U, (uint8_t)109U,
    (uint8_t)217U, (uint8_t)138U, (uint8_t)57U, (uint8_t)177U, (uint8_t)66U, (uint8_t)142U,
    (uint8_t)167U, (uint8_t)223U
  };

static uint8_t
vectors_low171[16U] =
  {
    (uint8_t)140U, (uint8_t)187U, (uint8_t)151U, (uint8_t)245U, (uint8_t)140U, (uint8_t)242U,
    (uint8_t)67U, (uint8_t)4U, (uint8_t)91U, (uint8_t)218U, (uint8_t)219U, (uint8_t)47U,
    (uint8_t)155U, (uint8_t)189U, (uint8_t)171U, (uint8_t)16U
  };

static uint8_t
vectors_low172[32U] =
  {
    (uint8_t)244U, (uint8_t)135U, (uint8_t)185U, (uint8_t)75U, (uint8_t)94U, (uint8_t)78U,
    (uint8_t)218U, (uint8_t)73U, (uint8_t)233U, (uint8_t)51U, (uint8_t)224U, (uint8_t)194U,
    (uint8_t)104U, (uint8_t)235U, (uint8_t)80U, (uint8_t)66U, (uint8_t)196U, (uint8_t)34U,
    (uint8_t)223U, (uint8_t)136U, (uint8_t)6U, (uint8_t)30U, (uint8_t)191U, (uint8_t)253U,
    (uint8_t)137U, (uint8_t)61U, (uint8_t)57U, (uint8_t)250U, (uint8_t)253U, (uint8_t)88U,
    (uint8_t)239U, (uint8_t)211U
  };

static uint8_t
vectors_low173[32U] =
  {
    (uint8_t)255U, (uint8_t)142U, (uint8_t)118U, (uint8_t)86U, (uint8_t)162U, (uint8_t)27U,
    (uint8_t)204U, (uint8_t)237U, (uint8_t)8U, (uint8_t)41U, (uint8_t)114U, (uint8_t)113U,
    (uint8_t)158U, (uint8_t)191U, (uint8_t)135U, (uint8_t)83U, (uint8_t)156U, (uint8_t)72U,
    (uint8_t)37U, (uint8_t)203U, (uint8_t)15U, (uint8_t)75U, (uint8_t)234U, (uint8_t)189U,
    (uint8_t)18U, (uint8_t)161U, (uint8_t)45U, (uint8_t)84U, (uint8_t)77U, (uint8_t)234U,
    (uint8_t)135U, (uint8_t)175U
  };

static uint8_t
vectors_low174[32U] =
  {
    (uint8_t)246U, (uint8_t)77U, (uint8_t)211U, (uint8_t)176U, (uint8_t)239U, (uint8_t)197U,
    (uint8_t)200U, (uint8_t)193U, (uint8_t)70U, (uint8_t)249U, (uint8_t)185U, (uint8_t)184U,
    (uint8_t)240U, (uint8_t)236U, (uint8_t)124U, (uint8_t)203U, (uint8_t)120U, (uint8_t)78U,
    (uint8_t)135U, (uint8_t)193U, (uint8_t)98U, (uint8_t)104U, (uint8_t)164U, (uint8_t)170U,
    (uint8_t)179U, (uint8_t)30U, (uint8_t)158U, (uint8_t)221U, (uint8_t)242U, (uint8_t)201U,
    (uint8_t)184U, (uint8_t)62U
  };

static uint8_t
vectors_low175[32U] =
  {
    (uint8_t)157U, (uint8_t)193U, (uint8_t)107U, (uint8_t)149U, (uint8_t)90U, (uint8_t)232U,
    (uint8_t)5U, (uint8_t)241U, (uint8_t)14U, (uint8_t)187U, (uint8_t)220U, (uint8_t)55U,
    (uint8_t)148U, (uint8_t)162U, (uint8_t)171U, (uint8_t)230U, (uint8_t)113U, (uint8_t)163U,
    (uint8_t)57U, (uint8_t)202U, (uint8_t)20U, (uint8_t)139U, (uint8_t)70U, (uint8_t)239U,
    (uint8_t)110U, (uint8_t)162U, (uint8_t)8U, (uint8_t)105U, (uint8_t)138U, (uint8_t)84U,
    (uint8_t)160U, (uint8_t)216U
  };

static uint8_t
vectors_low176[255U] =
  {
    (uint8_t)14U, (uint8_t)140U, (uint8_t)156U, (uint8_t)185U, (uint8_t)159U, (uint8_t)236U,
    (uint8_t)55U, (uint8_t)96U, (uint8_t)43U, (uint8_t)41U, (uint8_t)30U, (uint8_t)80U,
    (uint8_t)142U, (uint8_t)67U, (uint8_t)194U, (uint8_t)171U, (uint8_t)50U, (uint8_t)61U,
    (uint8_t)5U, (uint8_t)118U, (uint8_t)65U, (uint8_t)132U, (uint8_t)55U, (uint8_t)156U,
    (uint8_t)163U, (uint8_t)162U, (uint8_t)202U, (uint8_t)64U, (uint8_t)128U, (uint8_t)237U,
    (uint8_t)38U, (uint8_t)194U, (uint8_t)219U, (uint8_t)253U, (uint8_t)243U, (uint8_t)209U,
    (uint8_t)145U, (uint8_t)100U, (uint8_t)133U, (uint8_t)199U, (uint8_t)235U, (uint8_t)164U,
    (uint8_t)144U, (uint8_t)119U, (uint8_t)202U, (uint8_t)136U, (uint8_t)31U, (uint8_t)176U,
    (uint8_t)61U, (uint8_t)7U, (uint8_t)249U, (uint8_t)103U, (uint8_t)202U, (uint8_t)217U,
    (uint8_t)180U, (uint8_t)119U, (uint8_t)149U, (uint8_t)159U, (uint8_t)0U, (uint8_t)122U,
    (uint8_t)97U, (uint8_t)136U, (uint8_t)21U, (uint8_t)11U, (uint8_t)102U, (uint8_t)48U,
    (uint8_t)33U, (uint8_t)138U, (uint8_t)245U, (uint8_t)95U, (uint8_t)221U, (uint8_t)123U,
    (uint8_t)226U, (uint8_t)235U, (uint8_t)136U, (uint8_t)212U, (uint8_t)139U, (uint8_t)94U,
    (uint8_t)198U, (uint8_t)182U, (uint8_t)135U, (uint8_t)110U, (uint8_t)194U, (uint8_t)86U,
    (uint8_t)101U, (uint8_t)192U, (uint8_t)49U, (uint8_t)6U, (uint8_t)36U, (uint8_t)40U,
    (uint8_t)61U, (uint8_t)43U, (uint8_t)84U, (uint8_t)96U, (uint8_t)227U, (uint8_t)115U,
    (uint8_t)111U, (uint8_t)139U, (uint8_t)159U, (uint8_t)11U, (uint8_t)132U, (uint8_t)9U,
    (uint8_t)90U, (uint8_t)164U, (uint8_t)117U, (uint8_t)74U, (uint8_t)197U, (uint8_t)144U,
    (uint8_t)103U, (uint8_t)167U, (uint8_t)204U, (uint8_t)115U, (uint8_t)64U, (uint8_t)44U,
    (uint8_t)9U, (uint8_t)177U, (uint8_t)118U, (uint8_t)137U, (uint8_t)114U, (uint8_t)179U,
    (uint8_t)171U, (uint8_t)212U, (uint8_t)158U, (uint8_t)14U, (uint8_t)35U, (uint8_t)122U,
    (uint8_t)116U, (uint8_t)22U, (uint8_t)73U, (uint8_t)234U, (uint8_t)120U, (uint8_t)136U,
    (uint8_t)234U, (uint8_t)74U, (uint8_t)2U, (uint8_t)76U, (uint8_t)9U, (uint8_t)82U,
    (uint8_t)185U, (uint8_t)74U, (uint8_t)242U, (uint8_t)124U, (uint8_t)83U, (uint8_t)177U,
    (uint8_t)58U, (uint8_t)252U, (uint8_t)170U, (uint8_t)79U, (uint8_t)183U, (uint8_t)151U,
    (uint8_t)111U, (uint8_t)101U, (uint8_t)68U, (uint8_t)56U, (uint8_t)9U, (uint8_t)209U,
    (uint8_t)187U, (uint8_t)215U, (uint8_t)228U, (uint8_t)183U, (uint8_t)65U, (uint8_t)188U,
    (uint8_t)214U, (uint8_t)196U, (uint8_t)163U, (uint8_t)242U, (uint8_t)205U, (uint8_t)248U,
    (uint8_t)99U, (uint8_t)231U, (uint8_t)25U, (uint8_t)229U, (uint8_t)213U, (uint8_t)230U,
    (uint8_t)0U, (uint8_t)67U, (uint8_t)231U, (uint8_t)113U, (uint8_t)206U, (uint8_t)83U,
    (uint8_t)85U, (uint8_t)222U, (uint8_t)225U, (uint8_t)197U, (uint8_t)41U, (uint8_t)157U,
    (uint8_t)223U, (uint8_t)165U, (uint8_t)77U, (uint8_t)119U, (uint8_t)221U, (uint8_t)222U,
    (uint8_t)41U, (uint8_t)36U, (uint8_t)39U, (uint8_t)28U, (uint8_t)14U, (uint8_t)206U,
    (uint8_t)30U, (uint8_t)30U, (uint8_t)30U, (uint8_t)138U, (uint8_t)166U, (uint8_t)33U,
    (uint8_t)140U, (uint8_t)8U, (uint8_t)174U, (uint8_t)228U, (uint8_t)9U, (uint8_t)147U,
    (uint8_t)238U, (uint8_t)213U, (uint8_t)137U, (uint8_t)89U, (uint8_t)175U, (uint8_t)67U,
    (uint8_t)12U, (uint8_t)125U, (uint8_t)83U, (uint8_t)180U, (uint8_t)23U, (uint8_t)154U,
    (uint8_t)163U, (uint8_t)85U, (uint8_t)254U, (uint8_t)188U, (uint8_t)196U, (uint8_t)1U,
    (uint8_t)36U, (uint8_t)203U, (uint8_t)122U, (uint8_t)29U, (uint8_t)41U, (uint8_t)101U,
    (uint8_t)227U, (uint8_t)104U, (uint8_t)50U, (uint8_t)229U, (uint8_t)244U, (uint8_t)47U,
    (uint8_t)154U, (uint8_t)72U, (uint8_t)39U, (uint8_t)88U, (uint8_t)136U, (uint8_t)114U,
    (uint8_t)92U, (uint8_t)186U, (uint8_t)40U, (uint8_t)215U, (uint8_t)35U, (uint8_t)152U,
    (uint8_t)251U, (uint8_t)239U, (uint8_t)172U
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
__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_s
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
__Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t;

static __Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
vectors_low177[28U] =
  {
    {
      .fst = SHA1, .snd = { .len = (uint32_t)16U, .b = vectors_low0 },
      .thd = { .len = (uint32_t)8U, .b = vectors_low1 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)16U, .b = vectors_low2 },
      .f5 = { .len = (uint32_t)16U, .b = vectors_low3 },
      .f6 = {
        .fst = { .len = (uint32_t)16U, .b = vectors_low4 },
        .snd = { .len = (uint32_t)16U, .b = vectors_low5 }
      }, .f7 = { .len = (uint32_t)80U, .b = vectors_low6 }
    },
    {
      .fst = SHA1, .snd = { .len = (uint32_t)16U, .b = vectors_low7 },
      .thd = { .len = (uint32_t)8U, .b = vectors_low8 },
      .f3 = { .len = (uint32_t)16U, .b = vectors_low9 },
      .f4 = { .len = (uint32_t)16U, .b = vectors_low10 },
      .f5 = { .len = (uint32_t)16U, .b = vectors_low11 },
      .f6 = {
        .fst = { .len = (uint32_t)16U, .b = vectors_low12 },
        .snd = { .len = (uint32_t)16U, .b = vectors_low13 }
      }, .f7 = { .len = (uint32_t)80U, .b = vectors_low14 }
    },
    {
      .fst = SHA1, .snd = { .len = (uint32_t)16U, .b = vectors_low15 },
      .thd = { .len = (uint32_t)8U, .b = vectors_low16 },
      .f3 = { .len = (uint32_t)16U, .b = vectors_low17 },
      .f4 = { .len = (uint32_t)16U, .b = vectors_low18 }, .f5 = { .len = (uint32_t)0U, .b = NULL },
      .f6 = { .fst = { .len = (uint32_t)0U, .b = NULL }, .snd = { .len = (uint32_t)0U, .b = NULL } },
      .f7 = { .len = (uint32_t)80U, .b = vectors_low19 }
    },
    {
      .fst = SHA1, .snd = { .len = (uint32_t)16U, .b = vectors_low20 },
      .thd = { .len = (uint32_t)8U, .b = vectors_low21 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)16U, .b = vectors_low22 }, .f5 = { .len = (uint32_t)0U, .b = NULL },
      .f6 = { .fst = { .len = (uint32_t)0U, .b = NULL }, .snd = { .len = (uint32_t)0U, .b = NULL } },
      .f7 = { .len = (uint32_t)80U, .b = vectors_low23 }
    },
    {
      .fst = SHA1, .snd = { .len = (uint32_t)16U, .b = vectors_low24 },
      .thd = { .len = (uint32_t)8U, .b = vectors_low25 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)16U, .b = vectors_low26 },
      .f5 = { .len = (uint32_t)16U, .b = vectors_low27 },
      .f6 = {
        .fst = { .len = (uint32_t)16U, .b = vectors_low28 },
        .snd = { .len = (uint32_t)16U, .b = vectors_low29 }
      }, .f7 = { .len = (uint32_t)80U, .b = vectors_low30 }
    },
    {
      .fst = SHA1, .snd = { .len = (uint32_t)16U, .b = vectors_low31 },
      .thd = { .len = (uint32_t)8U, .b = vectors_low32 },
      .f3 = { .len = (uint32_t)16U, .b = vectors_low33 },
      .f4 = { .len = (uint32_t)16U, .b = vectors_low34 },
      .f5 = { .len = (uint32_t)16U, .b = vectors_low35 },
      .f6 = {
        .fst = { .len = (uint32_t)16U, .b = vectors_low36 },
        .snd = { .len = (uint32_t)16U, .b = vectors_low37 }
      }, .f7 = { .len = (uint32_t)80U, .b = vectors_low38 }
    },
    {
      .fst = SHA2_256, .snd = { .len = (uint32_t)32U, .b = vectors_low39 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low40 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low41 },
      .f5 = { .len = (uint32_t)32U, .b = vectors_low42 },
      .f6 = {
        .fst = { .len = (uint32_t)32U, .b = vectors_low43 },
        .snd = { .len = (uint32_t)32U, .b = vectors_low44 }
      }, .f7 = { .len = (uint32_t)128U, .b = vectors_low45 }
    },
    {
      .fst = SHA2_256, .snd = { .len = (uint32_t)32U, .b = vectors_low46 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low47 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low48 },
      .f5 = { .len = (uint32_t)32U, .b = vectors_low49 },
      .f6 = {
        .fst = { .len = (uint32_t)32U, .b = vectors_low50 },
        .snd = { .len = (uint32_t)32U, .b = vectors_low51 }
      }, .f7 = { .len = (uint32_t)128U, .b = vectors_low52 }
    },
    {
      .fst = SHA2_256, .snd = { .len = (uint32_t)32U, .b = vectors_low53 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low54 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low55 },
      .f5 = { .len = (uint32_t)32U, .b = vectors_low56 },
      .f6 = {
        .fst = { .len = (uint32_t)32U, .b = vectors_low57 },
        .snd = { .len = (uint32_t)32U, .b = vectors_low58 }
      }, .f7 = { .len = (uint32_t)128U, .b = vectors_low59 }
    },
    {
      .fst = SHA2_256, .snd = { .len = (uint32_t)32U, .b = vectors_low60 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low61 },
      .f3 = { .len = (uint32_t)32U, .b = vectors_low62 },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low63 },
      .f5 = { .len = (uint32_t)32U, .b = vectors_low64 },
      .f6 = {
        .fst = { .len = (uint32_t)32U, .b = vectors_low65 },
        .snd = { .len = (uint32_t)32U, .b = vectors_low66 }
      }, .f7 = { .len = (uint32_t)128U, .b = vectors_low67 }
    },
    {
      .fst = SHA2_256, .snd = { .len = (uint32_t)32U, .b = vectors_low68 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low69 },
      .f3 = { .len = (uint32_t)32U, .b = vectors_low70 },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low71 }, .f5 = { .len = (uint32_t)0U, .b = NULL },
      .f6 = { .fst = { .len = (uint32_t)0U, .b = NULL }, .snd = { .len = (uint32_t)0U, .b = NULL } },
      .f7 = { .len = (uint32_t)128U, .b = vectors_low72 }
    },
    {
      .fst = SHA2_256, .snd = { .len = (uint32_t)32U, .b = vectors_low73 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low74 },
      .f3 = { .len = (uint32_t)32U, .b = vectors_low75 },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low76 },
      .f5 = { .len = (uint32_t)32U, .b = vectors_low77 },
      .f6 = {
        .fst = { .len = (uint32_t)32U, .b = vectors_low78 },
        .snd = { .len = (uint32_t)32U, .b = vectors_low79 }
      }, .f7 = { .len = (uint32_t)128U, .b = vectors_low80 }
    },
    {
      .fst = SHA2_256, .snd = { .len = (uint32_t)32U, .b = vectors_low81 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low82 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low83 },
      .f5 = { .len = (uint32_t)32U, .b = vectors_low84 },
      .f6 = {
        .fst = { .len = (uint32_t)32U, .b = vectors_low85 },
        .snd = { .len = (uint32_t)32U, .b = vectors_low86 }
      }, .f7 = { .len = (uint32_t)128U, .b = vectors_low87 }
    },
    {
      .fst = SHA2_256, .snd = { .len = (uint32_t)32U, .b = vectors_low88 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low89 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low90 }, .f5 = { .len = (uint32_t)0U, .b = NULL },
      .f6 = { .fst = { .len = (uint32_t)0U, .b = NULL }, .snd = { .len = (uint32_t)0U, .b = NULL } },
      .f7 = { .len = (uint32_t)128U, .b = vectors_low91 }
    },
    {
      .fst = SHA2_256, .snd = { .len = (uint32_t)32U, .b = vectors_low92 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low93 },
      .f3 = { .len = (uint32_t)32U, .b = vectors_low94 },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low95 }, .f5 = { .len = (uint32_t)0U, .b = NULL },
      .f6 = { .fst = { .len = (uint32_t)0U, .b = NULL }, .snd = { .len = (uint32_t)0U, .b = NULL } },
      .f7 = { .len = (uint32_t)128U, .b = vectors_low96 }
    },
    {
      .fst = SHA2_384, .snd = { .len = (uint32_t)32U, .b = vectors_low97 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low98 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low99 },
      .f5 = { .len = (uint32_t)32U, .b = vectors_low100 },
      .f6 = {
        .fst = { .len = (uint32_t)32U, .b = vectors_low101 },
        .snd = { .len = (uint32_t)32U, .b = vectors_low102 }
      }, .f7 = { .len = (uint32_t)192U, .b = vectors_low103 }
    },
    {
      .fst = SHA2_384, .snd = { .len = (uint32_t)32U, .b = vectors_low104 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low105 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low106 }, .f5 = { .len = (uint32_t)0U, .b = NULL },
      .f6 = { .fst = { .len = (uint32_t)0U, .b = NULL }, .snd = { .len = (uint32_t)0U, .b = NULL } },
      .f7 = { .len = (uint32_t)192U, .b = vectors_low107 }
    },
    {
      .fst = SHA2_384, .snd = { .len = (uint32_t)32U, .b = vectors_low108 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low109 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low110 },
      .f5 = { .len = (uint32_t)32U, .b = vectors_low111 },
      .f6 = {
        .fst = { .len = (uint32_t)32U, .b = vectors_low112 },
        .snd = { .len = (uint32_t)32U, .b = vectors_low113 }
      }, .f7 = { .len = (uint32_t)192U, .b = vectors_low114 }
    },
    {
      .fst = SHA2_512, .snd = { .len = (uint32_t)32U, .b = vectors_low115 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low116 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low117 }, .f5 = { .len = (uint32_t)0U, .b = NULL },
      .f6 = { .fst = { .len = (uint32_t)0U, .b = NULL }, .snd = { .len = (uint32_t)0U, .b = NULL } },
      .f7 = { .len = (uint32_t)256U, .b = vectors_low118 }
    },
    {
      .fst = SHA2_512, .snd = { .len = (uint32_t)32U, .b = vectors_low119 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low120 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low121 }, .f5 = { .len = (uint32_t)0U, .b = NULL },
      .f6 = { .fst = { .len = (uint32_t)0U, .b = NULL }, .snd = { .len = (uint32_t)0U, .b = NULL } },
      .f7 = { .len = (uint32_t)256U, .b = vectors_low122 }
    },
    {
      .fst = SHA2_512, .snd = { .len = (uint32_t)32U, .b = vectors_low123 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low124 },
      .f3 = { .len = (uint32_t)32U, .b = vectors_low125 },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low126 }, .f5 = { .len = (uint32_t)0U, .b = NULL },
      .f6 = { .fst = { .len = (uint32_t)0U, .b = NULL }, .snd = { .len = (uint32_t)0U, .b = NULL } },
      .f7 = { .len = (uint32_t)256U, .b = vectors_low127 }
    },
    {
      .fst = SHA2_512, .snd = { .len = (uint32_t)32U, .b = vectors_low128 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low129 },
      .f3 = { .len = (uint32_t)32U, .b = vectors_low130 },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low131 },
      .f5 = { .len = (uint32_t)32U, .b = vectors_low132 },
      .f6 = {
        .fst = { .len = (uint32_t)32U, .b = vectors_low133 },
        .snd = { .len = (uint32_t)32U, .b = vectors_low134 }
      }, .f7 = { .len = (uint32_t)256U, .b = vectors_low135 }
    },
    {
      .fst = SHA2_512, .snd = { .len = (uint32_t)32U, .b = vectors_low136 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low137 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low138 }, .f5 = { .len = (uint32_t)0U, .b = NULL },
      .f6 = { .fst = { .len = (uint32_t)0U, .b = NULL }, .snd = { .len = (uint32_t)0U, .b = NULL } },
      .f7 = { .len = (uint32_t)256U, .b = vectors_low139 }
    },
    {
      .fst = SHA2_512, .snd = { .len = (uint32_t)32U, .b = vectors_low140 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low141 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low142 },
      .f5 = { .len = (uint32_t)32U, .b = vectors_low143 },
      .f6 = {
        .fst = { .len = (uint32_t)32U, .b = vectors_low144 },
        .snd = { .len = (uint32_t)32U, .b = vectors_low145 }
      }, .f7 = { .len = (uint32_t)256U, .b = vectors_low146 }
    },
    {
      .fst = SHA2_512, .snd = { .len = (uint32_t)32U, .b = vectors_low147 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low148 },
      .f3 = { .len = (uint32_t)32U, .b = vectors_low149 },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low150 },
      .f5 = { .len = (uint32_t)32U, .b = vectors_low151 },
      .f6 = {
        .fst = { .len = (uint32_t)32U, .b = vectors_low152 },
        .snd = { .len = (uint32_t)32U, .b = vectors_low153 }
      }, .f7 = { .len = (uint32_t)256U, .b = vectors_low154 }
    },
    {
      .fst = SHA2_512, .snd = { .len = (uint32_t)32U, .b = vectors_low155 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low156 },
      .f3 = { .len = (uint32_t)32U, .b = vectors_low157 },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low158 },
      .f5 = { .len = (uint32_t)32U, .b = vectors_low159 },
      .f6 = {
        .fst = { .len = (uint32_t)32U, .b = vectors_low160 },
        .snd = { .len = (uint32_t)32U, .b = vectors_low161 }
      }, .f7 = { .len = (uint32_t)256U, .b = vectors_low162 }
    },
    {
      .fst = SHA2_512, .snd = { .len = (uint32_t)32U, .b = vectors_low163 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low164 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low165 },
      .f5 = { .len = (uint32_t)32U, .b = vectors_low166 },
      .f6 = {
        .fst = { .len = (uint32_t)32U, .b = vectors_low167 },
        .snd = { .len = (uint32_t)32U, .b = vectors_low168 }
      }, .f7 = { .len = (uint32_t)256U, .b = vectors_low169 }
    },
    {
      .fst = SHA2_512, .snd = { .len = (uint32_t)32U, .b = vectors_low170 },
      .thd = { .len = (uint32_t)16U, .b = vectors_low171 }, .f3 = { .len = (uint32_t)0U, .b = NULL },
      .f4 = { .len = (uint32_t)32U, .b = vectors_low172 },
      .f5 = { .len = (uint32_t)32U, .b = vectors_low173 },
      .f6 = {
        .fst = { .len = (uint32_t)32U, .b = vectors_low174 },
        .snd = { .len = (uint32_t)32U, .b = vectors_low175 }
      }, .f7 = { .len = (uint32_t)255U, .b = vectors_low176 }
    }
  };

typedef struct
lbuffer__K___Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_s
{
  uint32_t len;
  __Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
  *b;
}
lbuffer__K___Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t;

static lbuffer__K___Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
vectors_low = { .len = (uint32_t)28U, .b = vectors_low177 };

static bool compare_and_print(uint8_t *b1, uint8_t *b2, uint32_t len)
{
  LowStar_Printf_print_string("Expected: ");
  LowStar_Printf_print_lmbuffer_u8(len, (uint8_t *)b1);
  LowStar_Printf_print_string("\n");
  LowStar_Printf_print_string("Computed: ");
  LowStar_Printf_print_lmbuffer_u8(len, (uint8_t *)b2);
  LowStar_Printf_print_string("\n");
  uint8_t res = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(b1[i], b2[i]);
    res = uu____0 & res;
  }
  uint8_t z = res;
  bool b = z == (uint8_t)255U;
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
  __Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
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
    && min_length(a) / (uint32_t)2U <= nonce_len
    && nonce_len <= max_length
    && personalization_string_len <= max_personalization_string_length
    && min_length(a) <= entropy_input_reseed_len
    && entropy_input_reseed_len <= max_length
    && additional_input_reseed_len <= max_additional_input_length
    && additional_input_1_len <= max_additional_input_length
    && additional_input_2_len <= max_additional_input_length
    && (uint32_t)0U < returned_bits_len
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
    uint32_t ctr = (uint32_t)1U;
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

exit_code main()
{
  C_String_print("[HMAC_DRBG]");
  C_String_print("\n");
  uint32_t len = vectors_low.len;
  __Spec_Hash_Definitions_hash_alg_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer__uint8_t___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
  *vs = vectors_low.b;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    LowStar_Printf_print_string("HMAC-DRBG Test ");
    LowStar_Printf_print_u32(i + (uint32_t)1U);
    LowStar_Printf_print_string("/");
    LowStar_Printf_print_u32(len);
    LowStar_Printf_print_string("\n");
    test_one(vs[i]);
  }
  return EXIT_SUCCESS;
}

