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


#include "internal/Hacl_Hash_SHA2.h"


#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"
static u32
h256[8U] =
  {
    (u32)0x6a09e667U, (u32)0xbb67ae85U, (u32)0x3c6ef372U, (u32)0xa54ff53aU, (u32)0x510e527fU,
    (u32)0x9b05688cU, (u32)0x1f83d9abU, (u32)0x5be0cd19U
  };

static u64
h384[8U] =
  {
    (u64)0xcbbb9d5dc1059ed8U, (u64)0x629a292a367cd507U, (u64)0x9159015a3070dd17U,
    (u64)0x152fecd8f70e5939U, (u64)0x67332667ffc00b31U, (u64)0x8eb44a8768581511U,
    (u64)0xdb0c2e0d64f98fa7U, (u64)0x47b5481dbefa4fa4U
  };

static u64
h512[8U] =
  {
    (u64)0x6a09e667f3bcc908U, (u64)0xbb67ae8584caa73bU, (u64)0x3c6ef372fe94f82bU,
    (u64)0xa54ff53a5f1d36f1U, (u64)0x510e527fade682d1U, (u64)0x9b05688c2b3e6c1fU,
    (u64)0x1f83d9abfb41bd6bU, (u64)0x5be0cd19137e2179U
  };

static u32
k224_256[64U] =
  {
    (u32)0x428a2f98U, (u32)0x71374491U, (u32)0xb5c0fbcfU, (u32)0xe9b5dba5U, (u32)0x3956c25bU,
    (u32)0x59f111f1U, (u32)0x923f82a4U, (u32)0xab1c5ed5U, (u32)0xd807aa98U, (u32)0x12835b01U,
    (u32)0x243185beU, (u32)0x550c7dc3U, (u32)0x72be5d74U, (u32)0x80deb1feU, (u32)0x9bdc06a7U,
    (u32)0xc19bf174U, (u32)0xe49b69c1U, (u32)0xefbe4786U, (u32)0x0fc19dc6U, (u32)0x240ca1ccU,
    (u32)0x2de92c6fU, (u32)0x4a7484aaU, (u32)0x5cb0a9dcU, (u32)0x76f988daU, (u32)0x983e5152U,
    (u32)0xa831c66dU, (u32)0xb00327c8U, (u32)0xbf597fc7U, (u32)0xc6e00bf3U, (u32)0xd5a79147U,
    (u32)0x06ca6351U, (u32)0x14292967U, (u32)0x27b70a85U, (u32)0x2e1b2138U, (u32)0x4d2c6dfcU,
    (u32)0x53380d13U, (u32)0x650a7354U, (u32)0x766a0abbU, (u32)0x81c2c92eU, (u32)0x92722c85U,
    (u32)0xa2bfe8a1U, (u32)0xa81a664bU, (u32)0xc24b8b70U, (u32)0xc76c51a3U, (u32)0xd192e819U,
    (u32)0xd6990624U, (u32)0xf40e3585U, (u32)0x106aa070U, (u32)0x19a4c116U, (u32)0x1e376c08U,
    (u32)0x2748774cU, (u32)0x34b0bcb5U, (u32)0x391c0cb3U, (u32)0x4ed8aa4aU, (u32)0x5b9cca4fU,
    (u32)0x682e6ff3U, (u32)0x748f82eeU, (u32)0x78a5636fU, (u32)0x84c87814U, (u32)0x8cc70208U,
    (u32)0x90befffaU, (u32)0xa4506cebU, (u32)0xbef9a3f7U, (u32)0xc67178f2U
  };

static u64
k384_512[80U] =
  {
    (u64)0x428a2f98d728ae22U, (u64)0x7137449123ef65cdU, (u64)0xb5c0fbcfec4d3b2fU,
    (u64)0xe9b5dba58189dbbcU, (u64)0x3956c25bf348b538U, (u64)0x59f111f1b605d019U,
    (u64)0x923f82a4af194f9bU, (u64)0xab1c5ed5da6d8118U, (u64)0xd807aa98a3030242U,
    (u64)0x12835b0145706fbeU, (u64)0x243185be4ee4b28cU, (u64)0x550c7dc3d5ffb4e2U,
    (u64)0x72be5d74f27b896fU, (u64)0x80deb1fe3b1696b1U, (u64)0x9bdc06a725c71235U,
    (u64)0xc19bf174cf692694U, (u64)0xe49b69c19ef14ad2U, (u64)0xefbe4786384f25e3U,
    (u64)0x0fc19dc68b8cd5b5U, (u64)0x240ca1cc77ac9c65U, (u64)0x2de92c6f592b0275U,
    (u64)0x4a7484aa6ea6e483U, (u64)0x5cb0a9dcbd41fbd4U, (u64)0x76f988da831153b5U,
    (u64)0x983e5152ee66dfabU, (u64)0xa831c66d2db43210U, (u64)0xb00327c898fb213fU,
    (u64)0xbf597fc7beef0ee4U, (u64)0xc6e00bf33da88fc2U, (u64)0xd5a79147930aa725U,
    (u64)0x06ca6351e003826fU, (u64)0x142929670a0e6e70U, (u64)0x27b70a8546d22ffcU,
    (u64)0x2e1b21385c26c926U, (u64)0x4d2c6dfc5ac42aedU, (u64)0x53380d139d95b3dfU,
    (u64)0x650a73548baf63deU, (u64)0x766a0abb3c77b2a8U, (u64)0x81c2c92e47edaee6U,
    (u64)0x92722c851482353bU, (u64)0xa2bfe8a14cf10364U, (u64)0xa81a664bbc423001U,
    (u64)0xc24b8b70d0f89791U, (u64)0xc76c51a30654be30U, (u64)0xd192e819d6ef5218U,
    (u64)0xd69906245565a910U, (u64)0xf40e35855771202aU, (u64)0x106aa07032bbd1b8U,
    (u64)0x19a4c116b8d2d0c8U, (u64)0x1e376c085141ab53U, (u64)0x2748774cdf8eeb99U,
    (u64)0x34b0bcb5e19b48a8U, (u64)0x391c0cb3c5c95a63U, (u64)0x4ed8aa4ae3418acbU,
    (u64)0x5b9cca4f7763e373U, (u64)0x682e6ff3d6b2b8a3U, (u64)0x748f82ee5defb2fcU,
    (u64)0x78a5636f43172f60U, (u64)0x84c87814a1f0ab72U, (u64)0x8cc702081a6439ecU,
    (u64)0x90befffa23631e28U, (u64)0xa4506cebde82bde9U, (u64)0xbef9a3f7b2c67915U,
    (u64)0xc67178f2e372532bU, (u64)0xca273eceea26619cU, (u64)0xd186b8c721c0c207U,
    (u64)0xeada7dd6cde0eb1eU, (u64)0xf57d4f7fee6ed178U, (u64)0x06f067aa72176fbaU,
    (u64)0x0a637dc5a2c898a6U, (u64)0x113f9804bef90daeU, (u64)0x1b710b35131c471bU,
    (u64)0x28db77f523047d84U, (u64)0x32caab7b40c72493U, (u64)0x3c9ebe0a15c9bebcU,
    (u64)0x431d67c49c100d4cU, (u64)0x4cc5d4becb3e42b6U, (u64)0x597f299cfc657e2aU,
    (u64)0x5fcb6fab3ad6faecU, (u64)0x6c44198c4a475817U
  };

void Hacl_Hash_Core_SHA2_init_256(u32 *s)
{
  u32 i;
  for (i = (u32)0U; i < (u32)8U; i++)
    s[i] = h256[i];
}

void Hacl_Hash_Core_SHA2_init_384(u64 *s)
{
  u32 i;
  for (i = (u32)0U; i < (u32)8U; i++)
    s[i] = h384[i];
}

void Hacl_Hash_Core_SHA2_init_512(u64 *s)
{
  u32 i;
  for (i = (u32)0U; i < (u32)8U; i++)
    s[i] = h512[i];
}

static void update_224(u32 *hash, u8 *block)
{
  u32 hash1[8U] = { 0U };
  u32 computed_ws[64U] = { 0U };
  {
    u32 i;
    for (i = (u32)0U; i < (u32)64U; i++)
      if (i < (u32)16U)
      {
        u8 *b = block + i * (u32)4U;
        u32 u = load32_be(b);
        computed_ws[i] = u;
      }
      else
      {
        u32 t16 = computed_ws[i - (u32)16U];
        u32 t15 = computed_ws[i - (u32)15U];
        u32 t7 = computed_ws[i - (u32)7U];
        u32 t2 = computed_ws[i - (u32)2U];
        u32
        s1 =
          (t2 >> (u32)17U | t2 << (u32)15U)
          ^ ((t2 >> (u32)19U | t2 << (u32)13U) ^ t2 >> (u32)10U);
        u32
        s0 =
          (t15 >> (u32)7U | t15 << (u32)25U)
          ^ ((t15 >> (u32)18U | t15 << (u32)14U) ^ t15 >> (u32)3U);
        u32 w = s1 + t7 + s0 + t16;
        computed_ws[i] = w;
      }
  }
  memcpy(hash1, hash, (u32)8U * sizeof (u32));
  {
    u32 i;
    for (i = (u32)0U; i < (u32)64U; i++)
    {
      u32 a0 = hash1[0U];
      u32 b0 = hash1[1U];
      u32 c0 = hash1[2U];
      u32 d0 = hash1[3U];
      u32 e0 = hash1[4U];
      u32 f0 = hash1[5U];
      u32 g0 = hash1[6U];
      u32 h02 = hash1[7U];
      u32 w = computed_ws[i];
      u32
      t1 =
        h02
        +
          ((e0 >> (u32)6U | e0 << (u32)26U)
          ^ ((e0 >> (u32)11U | e0 << (u32)21U) ^ (e0 >> (u32)25U | e0 << (u32)7U)))
        + ((e0 & f0) ^ (~e0 & g0))
        + k224_256[i]
        + w;
      u32
      t2 =
        ((a0 >> (u32)2U | a0 << (u32)30U)
        ^ ((a0 >> (u32)13U | a0 << (u32)19U) ^ (a0 >> (u32)22U | a0 << (u32)10U)))
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
  }
  {
    u32 i;
    for (i = (u32)0U; i < (u32)8U; i++)
    {
      u32 xi = hash[i];
      u32 yi = hash1[i];
      hash[i] = xi + yi;
    }
  }
}

static void update_256(u32 *hash, u8 *block)
{
  u32 hash1[8U] = { 0U };
  u32 computed_ws[64U] = { 0U };
  {
    u32 i;
    for (i = (u32)0U; i < (u32)64U; i++)
      if (i < (u32)16U)
      {
        u8 *b = block + i * (u32)4U;
        u32 u = load32_be(b);
        computed_ws[i] = u;
      }
      else
      {
        u32 t16 = computed_ws[i - (u32)16U];
        u32 t15 = computed_ws[i - (u32)15U];
        u32 t7 = computed_ws[i - (u32)7U];
        u32 t2 = computed_ws[i - (u32)2U];
        u32
        s1 =
          (t2 >> (u32)17U | t2 << (u32)15U)
          ^ ((t2 >> (u32)19U | t2 << (u32)13U) ^ t2 >> (u32)10U);
        u32
        s0 =
          (t15 >> (u32)7U | t15 << (u32)25U)
          ^ ((t15 >> (u32)18U | t15 << (u32)14U) ^ t15 >> (u32)3U);
        u32 w = s1 + t7 + s0 + t16;
        computed_ws[i] = w;
      }
  }
  memcpy(hash1, hash, (u32)8U * sizeof (u32));
  {
    u32 i;
    for (i = (u32)0U; i < (u32)64U; i++)
    {
      u32 a0 = hash1[0U];
      u32 b0 = hash1[1U];
      u32 c0 = hash1[2U];
      u32 d0 = hash1[3U];
      u32 e0 = hash1[4U];
      u32 f0 = hash1[5U];
      u32 g0 = hash1[6U];
      u32 h02 = hash1[7U];
      u32 w = computed_ws[i];
      u32
      t1 =
        h02
        +
          ((e0 >> (u32)6U | e0 << (u32)26U)
          ^ ((e0 >> (u32)11U | e0 << (u32)21U) ^ (e0 >> (u32)25U | e0 << (u32)7U)))
        + ((e0 & f0) ^ (~e0 & g0))
        + k224_256[i]
        + w;
      u32
      t2 =
        ((a0 >> (u32)2U | a0 << (u32)30U)
        ^ ((a0 >> (u32)13U | a0 << (u32)19U) ^ (a0 >> (u32)22U | a0 << (u32)10U)))
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
  }
  {
    u32 i;
    for (i = (u32)0U; i < (u32)8U; i++)
    {
      u32 xi = hash[i];
      u32 yi = hash1[i];
      hash[i] = xi + yi;
    }
  }
}

static void update_384(u64 *hash, u8 *block)
{
  u64 hash1[8U] = { 0U };
  u64 computed_ws[80U] = { 0U };
  {
    u32 i;
    for (i = (u32)0U; i < (u32)80U; i++)
      if (i < (u32)16U)
      {
        u8 *b = block + i * (u32)8U;
        u64 u = load64_be(b);
        computed_ws[i] = u;
      }
      else
      {
        u64 t16 = computed_ws[i - (u32)16U];
        u64 t15 = computed_ws[i - (u32)15U];
        u64 t7 = computed_ws[i - (u32)7U];
        u64 t2 = computed_ws[i - (u32)2U];
        u64
        s1 = (t2 >> (u32)19U | t2 << (u32)45U) ^ ((t2 >> (u32)61U | t2 << (u32)3U) ^ t2 >> (u32)6U);
        u64
        s0 =
          (t15 >> (u32)1U | t15 << (u32)63U)
          ^ ((t15 >> (u32)8U | t15 << (u32)56U) ^ t15 >> (u32)7U);
        u64 w = s1 + t7 + s0 + t16;
        computed_ws[i] = w;
      }
  }
  memcpy(hash1, hash, (u32)8U * sizeof (u64));
  {
    u32 i;
    for (i = (u32)0U; i < (u32)80U; i++)
    {
      u64 a0 = hash1[0U];
      u64 b0 = hash1[1U];
      u64 c0 = hash1[2U];
      u64 d0 = hash1[3U];
      u64 e0 = hash1[4U];
      u64 f0 = hash1[5U];
      u64 g0 = hash1[6U];
      u64 h02 = hash1[7U];
      u64 w = computed_ws[i];
      u64
      t1 =
        h02
        +
          ((e0 >> (u32)14U | e0 << (u32)50U)
          ^ ((e0 >> (u32)18U | e0 << (u32)46U) ^ (e0 >> (u32)41U | e0 << (u32)23U)))
        + ((e0 & f0) ^ (~e0 & g0))
        + k384_512[i]
        + w;
      u64
      t2 =
        ((a0 >> (u32)28U | a0 << (u32)36U)
        ^ ((a0 >> (u32)34U | a0 << (u32)30U) ^ (a0 >> (u32)39U | a0 << (u32)25U)))
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
  }
  {
    u32 i;
    for (i = (u32)0U; i < (u32)8U; i++)
    {
      u64 xi = hash[i];
      u64 yi = hash1[i];
      hash[i] = xi + yi;
    }
  }
}

static void update_512(u64 *hash, u8 *block)
{
  u64 hash1[8U] = { 0U };
  u64 computed_ws[80U] = { 0U };
  {
    u32 i;
    for (i = (u32)0U; i < (u32)80U; i++)
      if (i < (u32)16U)
      {
        u8 *b = block + i * (u32)8U;
        u64 u = load64_be(b);
        computed_ws[i] = u;
      }
      else
      {
        u64 t16 = computed_ws[i - (u32)16U];
        u64 t15 = computed_ws[i - (u32)15U];
        u64 t7 = computed_ws[i - (u32)7U];
        u64 t2 = computed_ws[i - (u32)2U];
        u64
        s1 = (t2 >> (u32)19U | t2 << (u32)45U) ^ ((t2 >> (u32)61U | t2 << (u32)3U) ^ t2 >> (u32)6U);
        u64
        s0 =
          (t15 >> (u32)1U | t15 << (u32)63U)
          ^ ((t15 >> (u32)8U | t15 << (u32)56U) ^ t15 >> (u32)7U);
        u64 w = s1 + t7 + s0 + t16;
        computed_ws[i] = w;
      }
  }
  memcpy(hash1, hash, (u32)8U * sizeof (u64));
  {
    u32 i;
    for (i = (u32)0U; i < (u32)80U; i++)
    {
      u64 a0 = hash1[0U];
      u64 b0 = hash1[1U];
      u64 c0 = hash1[2U];
      u64 d0 = hash1[3U];
      u64 e0 = hash1[4U];
      u64 f0 = hash1[5U];
      u64 g0 = hash1[6U];
      u64 h02 = hash1[7U];
      u64 w = computed_ws[i];
      u64
      t1 =
        h02
        +
          ((e0 >> (u32)14U | e0 << (u32)50U)
          ^ ((e0 >> (u32)18U | e0 << (u32)46U) ^ (e0 >> (u32)41U | e0 << (u32)23U)))
        + ((e0 & f0) ^ (~e0 & g0))
        + k384_512[i]
        + w;
      u64
      t2 =
        ((a0 >> (u32)28U | a0 << (u32)36U)
        ^ ((a0 >> (u32)34U | a0 << (u32)30U) ^ (a0 >> (u32)39U | a0 << (u32)25U)))
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
  }
  {
    u32 i;
    for (i = (u32)0U; i < (u32)8U; i++)
    {
      u64 xi = hash[i];
      u64 yi = hash1[i];
      hash[i] = xi + yi;
    }
  }
}

static void pad_224(u64 len, u8 *dst)
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

static void pad_256(u64 len, u8 *dst)
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

static void pad_384(uint128_t len, u8 *dst)
{
  u8 *dst1 = dst;
  u8 *dst2;
  u8 *dst3;
  uint128_t len_;
  dst1[0U] = (u8)0x80U;
  dst2 = dst + (u32)1U;
  {
    u32 i;
    for
    (i
      = (u32)0U;
      i
      < ((u32)256U - ((u32)17U + (u32)((uint64_t)len % (u64)(u32)128U))) % (u32)128U;
      i++)
      dst2[i] = (u8)0U;
  }
  dst3 =
    dst
    + (u32)1U + ((u32)256U - ((u32)17U + (u32)((uint64_t)len % (u64)(u32)128U))) % (u32)128U;
  len_ = len << (u32)3U;
  store128_be(dst3, len_);
}

static void pad_512(uint128_t len, u8 *dst)
{
  u8 *dst1 = dst;
  u8 *dst2;
  u8 *dst3;
  uint128_t len_;
  dst1[0U] = (u8)0x80U;
  dst2 = dst + (u32)1U;
  {
    u32 i;
    for
    (i
      = (u32)0U;
      i
      < ((u32)256U - ((u32)17U + (u32)((uint64_t)len % (u64)(u32)128U))) % (u32)128U;
      i++)
      dst2[i] = (u8)0U;
  }
  dst3 =
    dst
    + (u32)1U + ((u32)256U - ((u32)17U + (u32)((uint64_t)len % (u64)(u32)128U))) % (u32)128U;
  len_ = len << (u32)3U;
  store128_be(dst3, len_);
}

static void finish_224(u32 *s, u8 *dst)
{
  u32 *uu____0 = s;
  u32 i;
  for (i = (u32)0U; i < (u32)7U; i++)
    store32_be(dst + i * (u32)4U, uu____0[i]);
}

void Hacl_Hash_Core_SHA2_finish_256(u32 *s, u8 *dst)
{
  u32 *uu____0 = s;
  u32 i;
  for (i = (u32)0U; i < (u32)8U; i++)
    store32_be(dst + i * (u32)4U, uu____0[i]);
}

void Hacl_Hash_Core_SHA2_finish_384(u64 *s, u8 *dst)
{
  u64 *uu____0 = s;
  u32 i;
  for (i = (u32)0U; i < (u32)6U; i++)
    store64_be(dst + i * (u32)8U, uu____0[i]);
}

void Hacl_Hash_Core_SHA2_finish_512(u64 *s, u8 *dst)
{
  u64 *uu____0 = s;
  u32 i;
  for (i = (u32)0U; i < (u32)8U; i++)
    store64_be(dst + i * (u32)8U, uu____0[i]);
}

void Hacl_Hash_SHA2_update_multi_224(u32 *s, u8 *blocks, u32 n_blocks)
{
  u32 i;
  for (i = (u32)0U; i < n_blocks; i++)
  {
    u32 sz = (u32)64U;
    u8 *block = blocks + sz * i;
    update_224(s, block);
  }
}

void Hacl_Hash_SHA2_update_multi_256(u32 *s, u8 *blocks, u32 n_blocks)
{
  u32 i;
  for (i = (u32)0U; i < n_blocks; i++)
  {
    u32 sz = (u32)64U;
    u8 *block = blocks + sz * i;
    update_256(s, block);
  }
}

void Hacl_Hash_SHA2_update_multi_384(u64 *s, u8 *blocks, u32 n_blocks)
{
  u32 i;
  for (i = (u32)0U; i < n_blocks; i++)
  {
    u32 sz = (u32)128U;
    u8 *block = blocks + sz * i;
    update_384(s, block);
  }
}

void Hacl_Hash_SHA2_update_multi_512(u64 *s, u8 *blocks, u32 n_blocks)
{
  u32 i;
  for (i = (u32)0U; i < n_blocks; i++)
  {
    u32 sz = (u32)128U;
    u8 *block = blocks + sz * i;
    update_512(s, block);
  }
}

void Hacl_Hash_SHA2_update_last_224(u32 *s, u64 prev_len, u8 *input, u32 input_len)
{
  u32 blocks_n = input_len / (u32)64U;
  u32 blocks_len = blocks_n * (u32)64U;
  u8 *blocks = input;
  u32 rest_len = input_len - blocks_len;
  u8 *rest = input + blocks_len;
  u64 total_input_len;
  u32 pad_len;
  u32 tmp_len;
  Hacl_Hash_SHA2_update_multi_224(s, blocks, blocks_n);
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
    pad_224(total_input_len, tmp_pad);
    Hacl_Hash_SHA2_update_multi_224(s, tmp, tmp_len / (u32)64U);
  }
}

void Hacl_Hash_SHA2_update_last_256(u32 *s, u64 prev_len, u8 *input, u32 input_len)
{
  u32 blocks_n = input_len / (u32)64U;
  u32 blocks_len = blocks_n * (u32)64U;
  u8 *blocks = input;
  u32 rest_len = input_len - blocks_len;
  u8 *rest = input + blocks_len;
  u64 total_input_len;
  u32 pad_len;
  u32 tmp_len;
  Hacl_Hash_SHA2_update_multi_256(s, blocks, blocks_n);
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
    pad_256(total_input_len, tmp_pad);
    Hacl_Hash_SHA2_update_multi_256(s, tmp, tmp_len / (u32)64U);
  }
}

void Hacl_Hash_SHA2_update_last_384(u64 *s, uint128_t prev_len, u8 *input, u32 input_len)
{
  u32 blocks_n = input_len / (u32)128U;
  u32 blocks_len = blocks_n * (u32)128U;
  u8 *blocks = input;
  u32 rest_len = input_len - blocks_len;
  u8 *rest = input + blocks_len;
  uint128_t total_input_len;
  u32 pad_len;
  u32 tmp_len;
  Hacl_Hash_SHA2_update_multi_384(s, blocks, blocks_n);
  total_input_len = prev_len + (uint128_t)(u64)input_len;
  pad_len =
    (u32)1U
    + ((u32)256U - ((u32)17U + (u32)((uint64_t)total_input_len % (u64)(u32)128U))) % (u32)128U
    + (u32)16U;
  tmp_len = rest_len + pad_len;
  {
    u8 tmp_twoblocks[256U] = { 0U };
    u8 *tmp = tmp_twoblocks;
    u8 *tmp_rest = tmp;
    u8 *tmp_pad = tmp + rest_len;
    memcpy(tmp_rest, rest, rest_len * sizeof (u8));
    pad_384(total_input_len, tmp_pad);
    Hacl_Hash_SHA2_update_multi_384(s, tmp, tmp_len / (u32)128U);
  }
}

void Hacl_Hash_SHA2_update_last_512(u64 *s, uint128_t prev_len, u8 *input, u32 input_len)
{
  u32 blocks_n = input_len / (u32)128U;
  u32 blocks_len = blocks_n * (u32)128U;
  u8 *blocks = input;
  u32 rest_len = input_len - blocks_len;
  u8 *rest = input + blocks_len;
  uint128_t total_input_len;
  u32 pad_len;
  u32 tmp_len;
  Hacl_Hash_SHA2_update_multi_512(s, blocks, blocks_n);
  total_input_len = prev_len + (uint128_t)(u64)input_len;
  pad_len =
    (u32)1U
    + ((u32)256U - ((u32)17U + (u32)((uint64_t)total_input_len % (u64)(u32)128U))) % (u32)128U
    + (u32)16U;
  tmp_len = rest_len + pad_len;
  {
    u8 tmp_twoblocks[256U] = { 0U };
    u8 *tmp = tmp_twoblocks;
    u8 *tmp_rest = tmp;
    u8 *tmp_pad = tmp + rest_len;
    memcpy(tmp_rest, rest, rest_len * sizeof (u8));
    pad_512(total_input_len, tmp_pad);
    Hacl_Hash_SHA2_update_multi_512(s, tmp, tmp_len / (u32)128U);
  }
}

void Hacl_Hash_SHA2_hash_224(u8 *input, u32 input_len, u8 *dst)
{
  u32
  scrut[8U] =
    {
      (u32)0xc1059ed8U, (u32)0x367cd507U, (u32)0x3070dd17U, (u32)0xf70e5939U, (u32)0xffc00b31U,
      (u32)0x68581511U, (u32)0x64f98fa7U, (u32)0xbefa4fa4U
    };
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
    Hacl_Hash_SHA2_update_multi_224(s, blocks, blocks_n);
    Hacl_Hash_SHA2_update_last_224(s, (u64)blocks_len, rest, rest_len);
    finish_224(s, dst);
  }
}

void Hacl_Hash_SHA2_hash_256(u8 *input, u32 input_len, u8 *dst)
{
  u32
  scrut[8U] =
    {
      (u32)0x6a09e667U, (u32)0xbb67ae85U, (u32)0x3c6ef372U, (u32)0xa54ff53aU, (u32)0x510e527fU,
      (u32)0x9b05688cU, (u32)0x1f83d9abU, (u32)0x5be0cd19U
    };
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
    Hacl_Hash_SHA2_update_multi_256(s, blocks, blocks_n);
    Hacl_Hash_SHA2_update_last_256(s, (u64)blocks_len, rest, rest_len);
    Hacl_Hash_Core_SHA2_finish_256(s, dst);
  }
}

typedef u64 *___u64____;

void Hacl_Hash_SHA2_hash_384(u8 *input, u32 input_len, u8 *dst)
{
  u64
  scrut[8U] =
    {
      (u64)0xcbbb9d5dc1059ed8U, (u64)0x629a292a367cd507U, (u64)0x9159015a3070dd17U,
      (u64)0x152fecd8f70e5939U, (u64)0x67332667ffc00b31U, (u64)0x8eb44a8768581511U,
      (u64)0xdb0c2e0d64f98fa7U, (u64)0x47b5481dbefa4fa4U
    };
  u64 *s = scrut;
  u32 blocks_n0 = input_len / (u32)128U;
  u32 blocks_n1;
  if (input_len % (u32)128U == (u32)0U && blocks_n0 > (u32)0U)
    blocks_n1 = blocks_n0 - (u32)1U;
  else
    blocks_n1 = blocks_n0;
  {
    u32 blocks_len0 = blocks_n1 * (u32)128U;
    u8 *blocks0 = input;
    u32 rest_len0 = input_len - blocks_len0;
    u8 *rest0 = input + blocks_len0;
    u32 blocks_n = blocks_n1;
    u32 blocks_len = blocks_len0;
    u8 *blocks = blocks0;
    u32 rest_len = rest_len0;
    u8 *rest = rest0;
    Hacl_Hash_SHA2_update_multi_384(s, blocks, blocks_n);
    Hacl_Hash_SHA2_update_last_384(s, (uint128_t)(u64)blocks_len, rest, rest_len);
    Hacl_Hash_Core_SHA2_finish_384(s, dst);
  }
}

void Hacl_Hash_SHA2_hash_512(u8 *input, u32 input_len, u8 *dst)
{
  u64
  scrut[8U] =
    {
      (u64)0x6a09e667f3bcc908U, (u64)0xbb67ae8584caa73bU, (u64)0x3c6ef372fe94f82bU,
      (u64)0xa54ff53a5f1d36f1U, (u64)0x510e527fade682d1U, (u64)0x9b05688c2b3e6c1fU,
      (u64)0x1f83d9abfb41bd6bU, (u64)0x5be0cd19137e2179U
    };
  u64 *s = scrut;
  u32 blocks_n0 = input_len / (u32)128U;
  u32 blocks_n1;
  if (input_len % (u32)128U == (u32)0U && blocks_n0 > (u32)0U)
    blocks_n1 = blocks_n0 - (u32)1U;
  else
    blocks_n1 = blocks_n0;
  {
    u32 blocks_len0 = blocks_n1 * (u32)128U;
    u8 *blocks0 = input;
    u32 rest_len0 = input_len - blocks_len0;
    u8 *rest0 = input + blocks_len0;
    u32 blocks_n = blocks_n1;
    u32 blocks_len = blocks_len0;
    u8 *blocks = blocks0;
    u32 rest_len = rest_len0;
    u8 *rest = rest0;
    Hacl_Hash_SHA2_update_multi_512(s, blocks, blocks_n);
    Hacl_Hash_SHA2_update_last_512(s, (uint128_t)(u64)blocks_len, rest, rest_len);
    Hacl_Hash_Core_SHA2_finish_512(s, dst);
  }
}

