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


#include "internal/Should_not_be_here.h"



static const
uint32_t
h224[8U] =
  {
    (uint32_t)0xc1059ed8U, (uint32_t)0x367cd507U, (uint32_t)0x3070dd17U, (uint32_t)0xf70e5939U,
    (uint32_t)0xffc00b31U, (uint32_t)0x68581511U, (uint32_t)0x64f98fa7U, (uint32_t)0xbefa4fa4U
  };

static const
uint32_t
h256[8U] =
  {
    (uint32_t)0x6a09e667U, (uint32_t)0xbb67ae85U, (uint32_t)0x3c6ef372U, (uint32_t)0xa54ff53aU,
    (uint32_t)0x510e527fU, (uint32_t)0x9b05688cU, (uint32_t)0x1f83d9abU, (uint32_t)0x5be0cd19U
  };

static const
uint64_t
h384[8U] =
  {
    (uint64_t)0xcbbb9d5dc1059ed8U, (uint64_t)0x629a292a367cd507U, (uint64_t)0x9159015a3070dd17U,
    (uint64_t)0x152fecd8f70e5939U, (uint64_t)0x67332667ffc00b31U, (uint64_t)0x8eb44a8768581511U,
    (uint64_t)0xdb0c2e0d64f98fa7U, (uint64_t)0x47b5481dbefa4fa4U
  };

static const
uint64_t
h512[8U] =
  {
    (uint64_t)0x6a09e667f3bcc908U, (uint64_t)0xbb67ae8584caa73bU, (uint64_t)0x3c6ef372fe94f82bU,
    (uint64_t)0xa54ff53a5f1d36f1U, (uint64_t)0x510e527fade682d1U, (uint64_t)0x9b05688c2b3e6c1fU,
    (uint64_t)0x1f83d9abfb41bd6bU, (uint64_t)0x5be0cd19137e2179U
  };

static const
uint32_t
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

static const
uint64_t
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

inline void Hacl_SHA2_Scalar32_sha224_init(uint32_t *hash)
{
  uint32_t i;
  for (i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t *os = hash;
    uint32_t x = h224[i];
    os[i] = x;
  }
}

static inline void sha224_update(uint8_t *b, uint32_t *hash)
{
  uint32_t hash_old[8U] = { 0U };
  uint32_t ws[16U] = { 0U };
  uint8_t *b10;
  uint32_t u0;
  uint32_t u1;
  uint32_t u2;
  uint32_t u3;
  uint32_t u4;
  uint32_t u5;
  uint32_t u6;
  uint32_t u7;
  uint32_t u8;
  uint32_t u9;
  uint32_t u10;
  uint32_t u11;
  uint32_t u12;
  uint32_t u13;
  uint32_t u14;
  uint32_t u;
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (uint32_t));
  b10 = b;
  u0 = load32_be(b10);
  ws[0U] = u0;
  u1 = load32_be(b10 + (uint32_t)4U);
  ws[1U] = u1;
  u2 = load32_be(b10 + (uint32_t)8U);
  ws[2U] = u2;
  u3 = load32_be(b10 + (uint32_t)12U);
  ws[3U] = u3;
  u4 = load32_be(b10 + (uint32_t)16U);
  ws[4U] = u4;
  u5 = load32_be(b10 + (uint32_t)20U);
  ws[5U] = u5;
  u6 = load32_be(b10 + (uint32_t)24U);
  ws[6U] = u6;
  u7 = load32_be(b10 + (uint32_t)28U);
  ws[7U] = u7;
  u8 = load32_be(b10 + (uint32_t)32U);
  ws[8U] = u8;
  u9 = load32_be(b10 + (uint32_t)36U);
  ws[9U] = u9;
  u10 = load32_be(b10 + (uint32_t)40U);
  ws[10U] = u10;
  u11 = load32_be(b10 + (uint32_t)44U);
  ws[11U] = u11;
  u12 = load32_be(b10 + (uint32_t)48U);
  ws[12U] = u12;
  u13 = load32_be(b10 + (uint32_t)52U);
  ws[13U] = u13;
  u14 = load32_be(b10 + (uint32_t)56U);
  ws[14U] = u14;
  u = load32_be(b10 + (uint32_t)60U);
  ws[15U] = u;
  KRML_MAYBE_FOR4(i0,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    KRML_MAYBE_FOR16(i,
      (uint32_t)0U,
      (uint32_t)16U,
      (uint32_t)1U,
      uint32_t k_t = k224_256[(uint32_t)16U * i0 + i];
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
      hash[7U] = h12;);
    if (i0 < (uint32_t)3U)
    {
      KRML_MAYBE_FOR16(i,
        (uint32_t)0U,
        (uint32_t)16U,
        (uint32_t)1U,
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
        ws[i] = s1 + t7 + s0 + t16;);
    });
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t *os = hash;
    uint32_t x = hash[i] + hash_old[i];
    os[i] = x;);
}

inline void Hacl_SHA2_Scalar32_sha224_update_nblocks(uint32_t len, uint8_t *b, uint32_t *st)
{
  uint32_t blocks = len / (uint32_t)64U;
  uint32_t i;
  for (i = (uint32_t)0U; i < blocks; i++)
  {
    uint8_t *b0 = b;
    uint8_t *mb = b0 + i * (uint32_t)64U;
    sha224_update(mb, st);
  }
}

typedef struct ___uint8_t___uint8_t__s
{
  uint8_t *fst;
  uint8_t *snd;
}
___uint8_t___uint8_t_;

inline void
Hacl_SHA2_Scalar32_sha224_update_last(
  uint64_t totlen,
  uint32_t len,
  uint8_t *b,
  uint32_t *hash
)
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
  {
    uint32_t fin = blocks * (uint32_t)64U;
    uint8_t last[128U] = { 0U };
    uint8_t totlen_buf[8U] = { 0U };
    uint64_t total_len_bits = totlen << (uint32_t)3U;
    uint8_t *b0;
    uint8_t *last00;
    uint8_t *last10;
    store64_be(totlen_buf, total_len_bits);
    b0 = b;
    memcpy(last, b0, len * sizeof (uint8_t));
    last[len] = (uint8_t)0x80U;
    memcpy(last + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
    last00 = last;
    last10 = last + (uint32_t)64U;
    {
      ___uint8_t___uint8_t_ lit0;
      ___uint8_t___uint8_t_ scrut0;
      uint8_t *l0;
      uint8_t *l1;
      uint8_t *lb0;
      uint8_t *lb1;
      lit0.fst = last00;
      lit0.snd = last10;
      scrut0 = lit0;
      l0 = scrut0.fst;
      l1 = scrut0.snd;
      lb0 = l0;
      lb1 = l1;
      {
        ___uint8_t___uint8_t_ lit;
        ___uint8_t___uint8_t_ scrut;
        uint8_t *last0;
        uint8_t *last1;
        lit.fst = lb0;
        lit.snd = lb1;
        scrut = lit;
        last0 = scrut.fst;
        last1 = scrut.snd;
        sha224_update(last0, hash);
        if (blocks > (uint32_t)1U)
        {
          sha224_update(last1, hash);
          return;
        }
      }
    }
  }
}

inline void Hacl_SHA2_Scalar32_sha224_finish(uint32_t *st, uint8_t *h)
{
  uint8_t hbuf[32U] = { 0U };
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    store32_be(hbuf + i * (uint32_t)4U, st[i]););
  memcpy(h, hbuf, (uint32_t)28U * sizeof (uint8_t));
}

inline void Hacl_SHA2_Scalar32_sha256_init(uint32_t *hash)
{
  uint32_t i;
  for (i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t *os = hash;
    uint32_t x = h256[i];
    os[i] = x;
  }
}

static inline void sha256_update(uint8_t *b, uint32_t *hash)
{
  uint32_t hash_old[8U] = { 0U };
  uint32_t ws[16U] = { 0U };
  uint8_t *b10;
  uint32_t u0;
  uint32_t u1;
  uint32_t u2;
  uint32_t u3;
  uint32_t u4;
  uint32_t u5;
  uint32_t u6;
  uint32_t u7;
  uint32_t u8;
  uint32_t u9;
  uint32_t u10;
  uint32_t u11;
  uint32_t u12;
  uint32_t u13;
  uint32_t u14;
  uint32_t u;
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (uint32_t));
  b10 = b;
  u0 = load32_be(b10);
  ws[0U] = u0;
  u1 = load32_be(b10 + (uint32_t)4U);
  ws[1U] = u1;
  u2 = load32_be(b10 + (uint32_t)8U);
  ws[2U] = u2;
  u3 = load32_be(b10 + (uint32_t)12U);
  ws[3U] = u3;
  u4 = load32_be(b10 + (uint32_t)16U);
  ws[4U] = u4;
  u5 = load32_be(b10 + (uint32_t)20U);
  ws[5U] = u5;
  u6 = load32_be(b10 + (uint32_t)24U);
  ws[6U] = u6;
  u7 = load32_be(b10 + (uint32_t)28U);
  ws[7U] = u7;
  u8 = load32_be(b10 + (uint32_t)32U);
  ws[8U] = u8;
  u9 = load32_be(b10 + (uint32_t)36U);
  ws[9U] = u9;
  u10 = load32_be(b10 + (uint32_t)40U);
  ws[10U] = u10;
  u11 = load32_be(b10 + (uint32_t)44U);
  ws[11U] = u11;
  u12 = load32_be(b10 + (uint32_t)48U);
  ws[12U] = u12;
  u13 = load32_be(b10 + (uint32_t)52U);
  ws[13U] = u13;
  u14 = load32_be(b10 + (uint32_t)56U);
  ws[14U] = u14;
  u = load32_be(b10 + (uint32_t)60U);
  ws[15U] = u;
  KRML_MAYBE_FOR4(i0,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    KRML_MAYBE_FOR16(i,
      (uint32_t)0U,
      (uint32_t)16U,
      (uint32_t)1U,
      uint32_t k_t = k224_256[(uint32_t)16U * i0 + i];
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
      hash[7U] = h12;);
    if (i0 < (uint32_t)3U)
    {
      KRML_MAYBE_FOR16(i,
        (uint32_t)0U,
        (uint32_t)16U,
        (uint32_t)1U,
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
        ws[i] = s1 + t7 + s0 + t16;);
    });
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t *os = hash;
    uint32_t x = hash[i] + hash_old[i];
    os[i] = x;);
}

inline void Hacl_SHA2_Scalar32_sha256_update_nblocks(uint32_t len, uint8_t *b, uint32_t *st)
{
  uint32_t blocks = len / (uint32_t)64U;
  uint32_t i;
  for (i = (uint32_t)0U; i < blocks; i++)
  {
    uint8_t *b0 = b;
    uint8_t *mb = b0 + i * (uint32_t)64U;
    sha256_update(mb, st);
  }
}

inline void
Hacl_SHA2_Scalar32_sha256_update_last(
  uint64_t totlen,
  uint32_t len,
  uint8_t *b,
  uint32_t *hash
)
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
  {
    uint32_t fin = blocks * (uint32_t)64U;
    uint8_t last[128U] = { 0U };
    uint8_t totlen_buf[8U] = { 0U };
    uint64_t total_len_bits = totlen << (uint32_t)3U;
    uint8_t *b0;
    uint8_t *last00;
    uint8_t *last10;
    store64_be(totlen_buf, total_len_bits);
    b0 = b;
    memcpy(last, b0, len * sizeof (uint8_t));
    last[len] = (uint8_t)0x80U;
    memcpy(last + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
    last00 = last;
    last10 = last + (uint32_t)64U;
    {
      ___uint8_t___uint8_t_ lit0;
      ___uint8_t___uint8_t_ scrut0;
      uint8_t *l0;
      uint8_t *l1;
      uint8_t *lb0;
      uint8_t *lb1;
      lit0.fst = last00;
      lit0.snd = last10;
      scrut0 = lit0;
      l0 = scrut0.fst;
      l1 = scrut0.snd;
      lb0 = l0;
      lb1 = l1;
      {
        ___uint8_t___uint8_t_ lit;
        ___uint8_t___uint8_t_ scrut;
        uint8_t *last0;
        uint8_t *last1;
        lit.fst = lb0;
        lit.snd = lb1;
        scrut = lit;
        last0 = scrut.fst;
        last1 = scrut.snd;
        sha256_update(last0, hash);
        if (blocks > (uint32_t)1U)
        {
          sha256_update(last1, hash);
          return;
        }
      }
    }
  }
}

inline void Hacl_SHA2_Scalar32_sha256_finish(uint32_t *st, uint8_t *h)
{
  uint8_t hbuf[32U] = { 0U };
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    store32_be(hbuf + i * (uint32_t)4U, st[i]););
  memcpy(h, hbuf, (uint32_t)32U * sizeof (uint8_t));
}

inline void Hacl_SHA2_Scalar32_sha384_init(uint64_t *hash)
{
  uint32_t i;
  for (i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t *os = hash;
    uint64_t x = h384[i];
    os[i] = x;
  }
}

static inline void sha384_update(uint8_t *b, uint64_t *hash)
{
  uint64_t hash_old[8U] = { 0U };
  uint64_t ws[16U] = { 0U };
  uint8_t *b10;
  uint64_t u0;
  uint64_t u1;
  uint64_t u2;
  uint64_t u3;
  uint64_t u4;
  uint64_t u5;
  uint64_t u6;
  uint64_t u7;
  uint64_t u8;
  uint64_t u9;
  uint64_t u10;
  uint64_t u11;
  uint64_t u12;
  uint64_t u13;
  uint64_t u14;
  uint64_t u;
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (uint64_t));
  b10 = b;
  u0 = load64_be(b10);
  ws[0U] = u0;
  u1 = load64_be(b10 + (uint32_t)8U);
  ws[1U] = u1;
  u2 = load64_be(b10 + (uint32_t)16U);
  ws[2U] = u2;
  u3 = load64_be(b10 + (uint32_t)24U);
  ws[3U] = u3;
  u4 = load64_be(b10 + (uint32_t)32U);
  ws[4U] = u4;
  u5 = load64_be(b10 + (uint32_t)40U);
  ws[5U] = u5;
  u6 = load64_be(b10 + (uint32_t)48U);
  ws[6U] = u6;
  u7 = load64_be(b10 + (uint32_t)56U);
  ws[7U] = u7;
  u8 = load64_be(b10 + (uint32_t)64U);
  ws[8U] = u8;
  u9 = load64_be(b10 + (uint32_t)72U);
  ws[9U] = u9;
  u10 = load64_be(b10 + (uint32_t)80U);
  ws[10U] = u10;
  u11 = load64_be(b10 + (uint32_t)88U);
  ws[11U] = u11;
  u12 = load64_be(b10 + (uint32_t)96U);
  ws[12U] = u12;
  u13 = load64_be(b10 + (uint32_t)104U);
  ws[13U] = u13;
  u14 = load64_be(b10 + (uint32_t)112U);
  ws[14U] = u14;
  u = load64_be(b10 + (uint32_t)120U);
  ws[15U] = u;
  KRML_MAYBE_FOR5(i0,
    (uint32_t)0U,
    (uint32_t)5U,
    (uint32_t)1U,
    KRML_MAYBE_FOR16(i,
      (uint32_t)0U,
      (uint32_t)16U,
      (uint32_t)1U,
      uint64_t k_t = k384_512[(uint32_t)16U * i0 + i];
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
      hash[7U] = h12;);
    if (i0 < (uint32_t)4U)
    {
      KRML_MAYBE_FOR16(i,
        (uint32_t)0U,
        (uint32_t)16U,
        (uint32_t)1U,
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
        ws[i] = s1 + t7 + s0 + t16;);
    });
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t *os = hash;
    uint64_t x = hash[i] + hash_old[i];
    os[i] = x;);
}

inline void Hacl_SHA2_Scalar32_sha384_update_nblocks(uint32_t len, uint8_t *b, uint64_t *st)
{
  uint32_t blocks = len / (uint32_t)128U;
  uint32_t i;
  for (i = (uint32_t)0U; i < blocks; i++)
  {
    uint8_t *b0 = b;
    uint8_t *mb = b0 + i * (uint32_t)128U;
    sha384_update(mb, st);
  }
}

inline void
Hacl_SHA2_Scalar32_sha384_update_last(
  FStar_UInt128_uint128 totlen,
  uint32_t len,
  uint8_t *b,
  uint64_t *hash
)
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
  {
    uint32_t fin = blocks * (uint32_t)128U;
    uint8_t last[256U] = { 0U };
    uint8_t totlen_buf[16U] = { 0U };
    FStar_UInt128_uint128 total_len_bits = FStar_UInt128_shift_left(totlen, (uint32_t)3U);
    uint8_t *b0;
    uint8_t *last00;
    uint8_t *last10;
    store128_be(totlen_buf, total_len_bits);
    b0 = b;
    memcpy(last, b0, len * sizeof (uint8_t));
    last[len] = (uint8_t)0x80U;
    memcpy(last + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (uint8_t));
    last00 = last;
    last10 = last + (uint32_t)128U;
    {
      ___uint8_t___uint8_t_ lit0;
      ___uint8_t___uint8_t_ scrut0;
      uint8_t *l0;
      uint8_t *l1;
      uint8_t *lb0;
      uint8_t *lb1;
      lit0.fst = last00;
      lit0.snd = last10;
      scrut0 = lit0;
      l0 = scrut0.fst;
      l1 = scrut0.snd;
      lb0 = l0;
      lb1 = l1;
      {
        ___uint8_t___uint8_t_ lit;
        ___uint8_t___uint8_t_ scrut;
        uint8_t *last0;
        uint8_t *last1;
        lit.fst = lb0;
        lit.snd = lb1;
        scrut = lit;
        last0 = scrut.fst;
        last1 = scrut.snd;
        sha384_update(last0, hash);
        if (blocks > (uint32_t)1U)
        {
          sha384_update(last1, hash);
          return;
        }
      }
    }
  }
}

inline void Hacl_SHA2_Scalar32_sha384_finish(uint64_t *st, uint8_t *h)
{
  uint8_t hbuf[64U] = { 0U };
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    store64_be(hbuf + i * (uint32_t)8U, st[i]););
  memcpy(h, hbuf, (uint32_t)48U * sizeof (uint8_t));
}

inline void Hacl_SHA2_Scalar32_sha512_init(uint64_t *hash)
{
  uint32_t i;
  for (i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t *os = hash;
    uint64_t x = h512[i];
    os[i] = x;
  }
}

static inline void sha512_update(uint8_t *b, uint64_t *hash)
{
  uint64_t hash_old[8U] = { 0U };
  uint64_t ws[16U] = { 0U };
  uint8_t *b10;
  uint64_t u0;
  uint64_t u1;
  uint64_t u2;
  uint64_t u3;
  uint64_t u4;
  uint64_t u5;
  uint64_t u6;
  uint64_t u7;
  uint64_t u8;
  uint64_t u9;
  uint64_t u10;
  uint64_t u11;
  uint64_t u12;
  uint64_t u13;
  uint64_t u14;
  uint64_t u;
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (uint64_t));
  b10 = b;
  u0 = load64_be(b10);
  ws[0U] = u0;
  u1 = load64_be(b10 + (uint32_t)8U);
  ws[1U] = u1;
  u2 = load64_be(b10 + (uint32_t)16U);
  ws[2U] = u2;
  u3 = load64_be(b10 + (uint32_t)24U);
  ws[3U] = u3;
  u4 = load64_be(b10 + (uint32_t)32U);
  ws[4U] = u4;
  u5 = load64_be(b10 + (uint32_t)40U);
  ws[5U] = u5;
  u6 = load64_be(b10 + (uint32_t)48U);
  ws[6U] = u6;
  u7 = load64_be(b10 + (uint32_t)56U);
  ws[7U] = u7;
  u8 = load64_be(b10 + (uint32_t)64U);
  ws[8U] = u8;
  u9 = load64_be(b10 + (uint32_t)72U);
  ws[9U] = u9;
  u10 = load64_be(b10 + (uint32_t)80U);
  ws[10U] = u10;
  u11 = load64_be(b10 + (uint32_t)88U);
  ws[11U] = u11;
  u12 = load64_be(b10 + (uint32_t)96U);
  ws[12U] = u12;
  u13 = load64_be(b10 + (uint32_t)104U);
  ws[13U] = u13;
  u14 = load64_be(b10 + (uint32_t)112U);
  ws[14U] = u14;
  u = load64_be(b10 + (uint32_t)120U);
  ws[15U] = u;
  KRML_MAYBE_FOR5(i0,
    (uint32_t)0U,
    (uint32_t)5U,
    (uint32_t)1U,
    KRML_MAYBE_FOR16(i,
      (uint32_t)0U,
      (uint32_t)16U,
      (uint32_t)1U,
      uint64_t k_t = k384_512[(uint32_t)16U * i0 + i];
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
      hash[7U] = h12;);
    if (i0 < (uint32_t)4U)
    {
      KRML_MAYBE_FOR16(i,
        (uint32_t)0U,
        (uint32_t)16U,
        (uint32_t)1U,
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
        ws[i] = s1 + t7 + s0 + t16;);
    });
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t *os = hash;
    uint64_t x = hash[i] + hash_old[i];
    os[i] = x;);
}

inline void Hacl_SHA2_Scalar32_sha512_update_nblocks(uint32_t len, uint8_t *b, uint64_t *st)
{
  uint32_t blocks = len / (uint32_t)128U;
  uint32_t i;
  for (i = (uint32_t)0U; i < blocks; i++)
  {
    uint8_t *b0 = b;
    uint8_t *mb = b0 + i * (uint32_t)128U;
    sha512_update(mb, st);
  }
}

inline void
Hacl_SHA2_Scalar32_sha512_update_last(
  FStar_UInt128_uint128 totlen,
  uint32_t len,
  uint8_t *b,
  uint64_t *hash
)
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
  {
    uint32_t fin = blocks * (uint32_t)128U;
    uint8_t last[256U] = { 0U };
    uint8_t totlen_buf[16U] = { 0U };
    FStar_UInt128_uint128 total_len_bits = FStar_UInt128_shift_left(totlen, (uint32_t)3U);
    uint8_t *b0;
    uint8_t *last00;
    uint8_t *last10;
    store128_be(totlen_buf, total_len_bits);
    b0 = b;
    memcpy(last, b0, len * sizeof (uint8_t));
    last[len] = (uint8_t)0x80U;
    memcpy(last + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (uint8_t));
    last00 = last;
    last10 = last + (uint32_t)128U;
    {
      ___uint8_t___uint8_t_ lit0;
      ___uint8_t___uint8_t_ scrut0;
      uint8_t *l0;
      uint8_t *l1;
      uint8_t *lb0;
      uint8_t *lb1;
      lit0.fst = last00;
      lit0.snd = last10;
      scrut0 = lit0;
      l0 = scrut0.fst;
      l1 = scrut0.snd;
      lb0 = l0;
      lb1 = l1;
      {
        ___uint8_t___uint8_t_ lit;
        ___uint8_t___uint8_t_ scrut;
        uint8_t *last0;
        uint8_t *last1;
        lit.fst = lb0;
        lit.snd = lb1;
        scrut = lit;
        last0 = scrut.fst;
        last1 = scrut.snd;
        sha512_update(last0, hash);
        if (blocks > (uint32_t)1U)
        {
          sha512_update(last1, hash);
          return;
        }
      }
    }
  }
}

inline void Hacl_SHA2_Scalar32_sha512_finish(uint64_t *st, uint8_t *h)
{
  uint8_t hbuf[64U] = { 0U };
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    store64_be(hbuf + i * (uint32_t)8U, st[i]););
  memcpy(h, hbuf, (uint32_t)64U * sizeof (uint8_t));
}

