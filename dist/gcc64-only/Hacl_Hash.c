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


#include "Hacl_Hash.h"

void Hacl_Hash_MD5_legacy_update_multi(uint32_t *s, uint8_t *blocks, uint32_t n_blocks)
{
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i = i + (uint32_t)1U)
  {
    uint32_t sz = (uint32_t)64U;
    uint8_t *block = blocks + sz * i;
    Hacl_Hash_Core_MD5_legacy_update(s, block);
  }
}

void
Hacl_Hash_MD5_legacy_update_last(
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
  Hacl_Hash_MD5_legacy_update_multi(s, blocks, blocks_n);
  uint64_t total_input_len = prev_len + (uint64_t)input_len;
  uint32_t
  pad_len1 =
    (uint32_t)1U
    +
      ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(total_input_len % (uint64_t)(uint32_t)64U)))
      % (uint32_t)64U
    + (uint32_t)8U;
  uint32_t tmp_len = rest_len + pad_len1;
  uint8_t tmp_twoblocks[128U] = { 0U };
  uint8_t *tmp = tmp_twoblocks;
  uint8_t *tmp_rest = tmp;
  uint8_t *tmp_pad = tmp + rest_len;
  memcpy(tmp_rest, rest, rest_len * sizeof rest[0U]);
  Hacl_Hash_Core_MD5_legacy_pad(total_input_len, tmp_pad);
  Hacl_Hash_MD5_legacy_update_multi(s, tmp, tmp_len / (uint32_t)64U);
}

void Hacl_Hash_MD5_legacy_hash(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint32_t
  s[4U] =
    { (uint32_t)0x67452301U, (uint32_t)0xefcdab89U, (uint32_t)0x98badcfeU, (uint32_t)0x10325476U };
  uint32_t blocks_n = input_len / (uint32_t)64U;
  uint32_t blocks_len = blocks_n * (uint32_t)64U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  Hacl_Hash_MD5_legacy_update_multi(s, blocks, blocks_n);
  Hacl_Hash_MD5_legacy_update_last(s, (uint64_t)blocks_len, rest, rest_len);
  Hacl_Hash_Core_MD5_legacy_finish(s, dst);
}

static uint32_t
Hacl_Hash_Core_MD5__h0[4U] =
  { (uint32_t)0x67452301U, (uint32_t)0xefcdab89U, (uint32_t)0x98badcfeU, (uint32_t)0x10325476U };

static uint32_t
Hacl_Hash_Core_MD5__t[64U] =
  {
    (uint32_t)0xd76aa478U, (uint32_t)0xe8c7b756U, (uint32_t)0x242070dbU, (uint32_t)0xc1bdceeeU,
    (uint32_t)0xf57c0fafU, (uint32_t)0x4787c62aU, (uint32_t)0xa8304613U, (uint32_t)0xfd469501U,
    (uint32_t)0x698098d8U, (uint32_t)0x8b44f7afU, (uint32_t)0xffff5bb1U, (uint32_t)0x895cd7beU,
    (uint32_t)0x6b901122U, (uint32_t)0xfd987193U, (uint32_t)0xa679438eU, (uint32_t)0x49b40821U,
    (uint32_t)0xf61e2562U, (uint32_t)0xc040b340U, (uint32_t)0x265e5a51U, (uint32_t)0xe9b6c7aaU,
    (uint32_t)0xd62f105dU, (uint32_t)0x02441453U, (uint32_t)0xd8a1e681U, (uint32_t)0xe7d3fbc8U,
    (uint32_t)0x21e1cde6U, (uint32_t)0xc33707d6U, (uint32_t)0xf4d50d87U, (uint32_t)0x455a14edU,
    (uint32_t)0xa9e3e905U, (uint32_t)0xfcefa3f8U, (uint32_t)0x676f02d9U, (uint32_t)0x8d2a4c8aU,
    (uint32_t)0xfffa3942U, (uint32_t)0x8771f681U, (uint32_t)0x6d9d6122U, (uint32_t)0xfde5380cU,
    (uint32_t)0xa4beea44U, (uint32_t)0x4bdecfa9U, (uint32_t)0xf6bb4b60U, (uint32_t)0xbebfbc70U,
    (uint32_t)0x289b7ec6U, (uint32_t)0xeaa127faU, (uint32_t)0xd4ef3085U, (uint32_t)0x4881d05U,
    (uint32_t)0xd9d4d039U, (uint32_t)0xe6db99e5U, (uint32_t)0x1fa27cf8U, (uint32_t)0xc4ac5665U,
    (uint32_t)0xf4292244U, (uint32_t)0x432aff97U, (uint32_t)0xab9423a7U, (uint32_t)0xfc93a039U,
    (uint32_t)0x655b59c3U, (uint32_t)0x8f0ccc92U, (uint32_t)0xffeff47dU, (uint32_t)0x85845dd1U,
    (uint32_t)0x6fa87e4fU, (uint32_t)0xfe2ce6e0U, (uint32_t)0xa3014314U, (uint32_t)0x4e0811a1U,
    (uint32_t)0xf7537e82U, (uint32_t)0xbd3af235U, (uint32_t)0x2ad7d2bbU, (uint32_t)0xeb86d391U
  };

void Hacl_Hash_Core_MD5_legacy_init(uint32_t *s)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
  {
    s[i] = Hacl_Hash_Core_MD5__h0[i];
  }
}

void Hacl_Hash_Core_MD5_legacy_update(uint32_t *abcd, uint8_t *x)
{
  uint32_t aa = abcd[0U];
  uint32_t bb = abcd[1U];
  uint32_t cc = abcd[2U];
  uint32_t dd = abcd[3U];
  uint32_t va = abcd[0U];
  uint32_t vb0 = abcd[1U];
  uint32_t vc0 = abcd[2U];
  uint32_t vd0 = abcd[3U];
  uint8_t *b0 = x;
  uint32_t u = load32_le(b0);
  uint32_t xk = u;
  uint32_t ti0 = Hacl_Hash_Core_MD5__t[0U];
  uint32_t
  v1 =
    vb0
    +
      ((va + ((vb0 & vc0) | (~vb0 & vd0)) + xk + ti0)
      << (uint32_t)7U
      | (va + ((vb0 & vc0) | (~vb0 & vd0)) + xk + ti0) >> (uint32_t)25U);
  abcd[0U] = v1;
  uint32_t va0 = abcd[3U];
  uint32_t vb1 = abcd[0U];
  uint32_t vc1 = abcd[1U];
  uint32_t vd1 = abcd[2U];
  uint8_t *b1 = x + (uint32_t)4U;
  uint32_t u0 = load32_le(b1);
  uint32_t xk0 = u0;
  uint32_t ti1 = Hacl_Hash_Core_MD5__t[1U];
  uint32_t
  v10 =
    vb1
    +
      ((va0 + ((vb1 & vc1) | (~vb1 & vd1)) + xk0 + ti1)
      << (uint32_t)12U
      | (va0 + ((vb1 & vc1) | (~vb1 & vd1)) + xk0 + ti1) >> (uint32_t)20U);
  abcd[3U] = v10;
  uint32_t va1 = abcd[2U];
  uint32_t vb2 = abcd[3U];
  uint32_t vc2 = abcd[0U];
  uint32_t vd2 = abcd[1U];
  uint8_t *b2 = x + (uint32_t)8U;
  uint32_t u1 = load32_le(b2);
  uint32_t xk1 = u1;
  uint32_t ti2 = Hacl_Hash_Core_MD5__t[2U];
  uint32_t
  v11 =
    vb2
    +
      ((va1 + ((vb2 & vc2) | (~vb2 & vd2)) + xk1 + ti2)
      << (uint32_t)17U
      | (va1 + ((vb2 & vc2) | (~vb2 & vd2)) + xk1 + ti2) >> (uint32_t)15U);
  abcd[2U] = v11;
  uint32_t va2 = abcd[1U];
  uint32_t vb3 = abcd[2U];
  uint32_t vc3 = abcd[3U];
  uint32_t vd3 = abcd[0U];
  uint8_t *b3 = x + (uint32_t)12U;
  uint32_t u2 = load32_le(b3);
  uint32_t xk2 = u2;
  uint32_t ti3 = Hacl_Hash_Core_MD5__t[3U];
  uint32_t
  v12 =
    vb3
    +
      ((va2 + ((vb3 & vc3) | (~vb3 & vd3)) + xk2 + ti3)
      << (uint32_t)22U
      | (va2 + ((vb3 & vc3) | (~vb3 & vd3)) + xk2 + ti3) >> (uint32_t)10U);
  abcd[1U] = v12;
  uint32_t va3 = abcd[0U];
  uint32_t vb4 = abcd[1U];
  uint32_t vc4 = abcd[2U];
  uint32_t vd4 = abcd[3U];
  uint8_t *b4 = x + (uint32_t)16U;
  uint32_t u3 = load32_le(b4);
  uint32_t xk3 = u3;
  uint32_t ti4 = Hacl_Hash_Core_MD5__t[4U];
  uint32_t
  v13 =
    vb4
    +
      ((va3 + ((vb4 & vc4) | (~vb4 & vd4)) + xk3 + ti4)
      << (uint32_t)7U
      | (va3 + ((vb4 & vc4) | (~vb4 & vd4)) + xk3 + ti4) >> (uint32_t)25U);
  abcd[0U] = v13;
  uint32_t va4 = abcd[3U];
  uint32_t vb5 = abcd[0U];
  uint32_t vc5 = abcd[1U];
  uint32_t vd5 = abcd[2U];
  uint8_t *b5 = x + (uint32_t)20U;
  uint32_t u4 = load32_le(b5);
  uint32_t xk4 = u4;
  uint32_t ti5 = Hacl_Hash_Core_MD5__t[5U];
  uint32_t
  v14 =
    vb5
    +
      ((va4 + ((vb5 & vc5) | (~vb5 & vd5)) + xk4 + ti5)
      << (uint32_t)12U
      | (va4 + ((vb5 & vc5) | (~vb5 & vd5)) + xk4 + ti5) >> (uint32_t)20U);
  abcd[3U] = v14;
  uint32_t va5 = abcd[2U];
  uint32_t vb6 = abcd[3U];
  uint32_t vc6 = abcd[0U];
  uint32_t vd6 = abcd[1U];
  uint8_t *b6 = x + (uint32_t)24U;
  uint32_t u5 = load32_le(b6);
  uint32_t xk5 = u5;
  uint32_t ti6 = Hacl_Hash_Core_MD5__t[6U];
  uint32_t
  v15 =
    vb6
    +
      ((va5 + ((vb6 & vc6) | (~vb6 & vd6)) + xk5 + ti6)
      << (uint32_t)17U
      | (va5 + ((vb6 & vc6) | (~vb6 & vd6)) + xk5 + ti6) >> (uint32_t)15U);
  abcd[2U] = v15;
  uint32_t va6 = abcd[1U];
  uint32_t vb7 = abcd[2U];
  uint32_t vc7 = abcd[3U];
  uint32_t vd7 = abcd[0U];
  uint8_t *b7 = x + (uint32_t)28U;
  uint32_t u6 = load32_le(b7);
  uint32_t xk6 = u6;
  uint32_t ti7 = Hacl_Hash_Core_MD5__t[7U];
  uint32_t
  v16 =
    vb7
    +
      ((va6 + ((vb7 & vc7) | (~vb7 & vd7)) + xk6 + ti7)
      << (uint32_t)22U
      | (va6 + ((vb7 & vc7) | (~vb7 & vd7)) + xk6 + ti7) >> (uint32_t)10U);
  abcd[1U] = v16;
  uint32_t va7 = abcd[0U];
  uint32_t vb8 = abcd[1U];
  uint32_t vc8 = abcd[2U];
  uint32_t vd8 = abcd[3U];
  uint8_t *b8 = x + (uint32_t)32U;
  uint32_t u7 = load32_le(b8);
  uint32_t xk7 = u7;
  uint32_t ti8 = Hacl_Hash_Core_MD5__t[8U];
  uint32_t
  v17 =
    vb8
    +
      ((va7 + ((vb8 & vc8) | (~vb8 & vd8)) + xk7 + ti8)
      << (uint32_t)7U
      | (va7 + ((vb8 & vc8) | (~vb8 & vd8)) + xk7 + ti8) >> (uint32_t)25U);
  abcd[0U] = v17;
  uint32_t va8 = abcd[3U];
  uint32_t vb9 = abcd[0U];
  uint32_t vc9 = abcd[1U];
  uint32_t vd9 = abcd[2U];
  uint8_t *b9 = x + (uint32_t)36U;
  uint32_t u8 = load32_le(b9);
  uint32_t xk8 = u8;
  uint32_t ti9 = Hacl_Hash_Core_MD5__t[9U];
  uint32_t
  v18 =
    vb9
    +
      ((va8 + ((vb9 & vc9) | (~vb9 & vd9)) + xk8 + ti9)
      << (uint32_t)12U
      | (va8 + ((vb9 & vc9) | (~vb9 & vd9)) + xk8 + ti9) >> (uint32_t)20U);
  abcd[3U] = v18;
  uint32_t va9 = abcd[2U];
  uint32_t vb10 = abcd[3U];
  uint32_t vc10 = abcd[0U];
  uint32_t vd10 = abcd[1U];
  uint8_t *b10 = x + (uint32_t)40U;
  uint32_t u9 = load32_le(b10);
  uint32_t xk9 = u9;
  uint32_t ti10 = Hacl_Hash_Core_MD5__t[10U];
  uint32_t
  v19 =
    vb10
    +
      ((va9 + ((vb10 & vc10) | (~vb10 & vd10)) + xk9 + ti10)
      << (uint32_t)17U
      | (va9 + ((vb10 & vc10) | (~vb10 & vd10)) + xk9 + ti10) >> (uint32_t)15U);
  abcd[2U] = v19;
  uint32_t va10 = abcd[1U];
  uint32_t vb11 = abcd[2U];
  uint32_t vc11 = abcd[3U];
  uint32_t vd11 = abcd[0U];
  uint8_t *b11 = x + (uint32_t)44U;
  uint32_t u10 = load32_le(b11);
  uint32_t xk10 = u10;
  uint32_t ti11 = Hacl_Hash_Core_MD5__t[11U];
  uint32_t
  v110 =
    vb11
    +
      ((va10 + ((vb11 & vc11) | (~vb11 & vd11)) + xk10 + ti11)
      << (uint32_t)22U
      | (va10 + ((vb11 & vc11) | (~vb11 & vd11)) + xk10 + ti11) >> (uint32_t)10U);
  abcd[1U] = v110;
  uint32_t va11 = abcd[0U];
  uint32_t vb12 = abcd[1U];
  uint32_t vc12 = abcd[2U];
  uint32_t vd12 = abcd[3U];
  uint8_t *b12 = x + (uint32_t)48U;
  uint32_t u11 = load32_le(b12);
  uint32_t xk11 = u11;
  uint32_t ti12 = Hacl_Hash_Core_MD5__t[12U];
  uint32_t
  v111 =
    vb12
    +
      ((va11 + ((vb12 & vc12) | (~vb12 & vd12)) + xk11 + ti12)
      << (uint32_t)7U
      | (va11 + ((vb12 & vc12) | (~vb12 & vd12)) + xk11 + ti12) >> (uint32_t)25U);
  abcd[0U] = v111;
  uint32_t va12 = abcd[3U];
  uint32_t vb13 = abcd[0U];
  uint32_t vc13 = abcd[1U];
  uint32_t vd13 = abcd[2U];
  uint8_t *b13 = x + (uint32_t)52U;
  uint32_t u12 = load32_le(b13);
  uint32_t xk12 = u12;
  uint32_t ti13 = Hacl_Hash_Core_MD5__t[13U];
  uint32_t
  v112 =
    vb13
    +
      ((va12 + ((vb13 & vc13) | (~vb13 & vd13)) + xk12 + ti13)
      << (uint32_t)12U
      | (va12 + ((vb13 & vc13) | (~vb13 & vd13)) + xk12 + ti13) >> (uint32_t)20U);
  abcd[3U] = v112;
  uint32_t va13 = abcd[2U];
  uint32_t vb14 = abcd[3U];
  uint32_t vc14 = abcd[0U];
  uint32_t vd14 = abcd[1U];
  uint8_t *b14 = x + (uint32_t)56U;
  uint32_t u13 = load32_le(b14);
  uint32_t xk13 = u13;
  uint32_t ti14 = Hacl_Hash_Core_MD5__t[14U];
  uint32_t
  v113 =
    vb14
    +
      ((va13 + ((vb14 & vc14) | (~vb14 & vd14)) + xk13 + ti14)
      << (uint32_t)17U
      | (va13 + ((vb14 & vc14) | (~vb14 & vd14)) + xk13 + ti14) >> (uint32_t)15U);
  abcd[2U] = v113;
  uint32_t va14 = abcd[1U];
  uint32_t vb15 = abcd[2U];
  uint32_t vc15 = abcd[3U];
  uint32_t vd15 = abcd[0U];
  uint8_t *b15 = x + (uint32_t)60U;
  uint32_t u14 = load32_le(b15);
  uint32_t xk14 = u14;
  uint32_t ti15 = Hacl_Hash_Core_MD5__t[15U];
  uint32_t
  v114 =
    vb15
    +
      ((va14 + ((vb15 & vc15) | (~vb15 & vd15)) + xk14 + ti15)
      << (uint32_t)22U
      | (va14 + ((vb15 & vc15) | (~vb15 & vd15)) + xk14 + ti15) >> (uint32_t)10U);
  abcd[1U] = v114;
  uint32_t va15 = abcd[0U];
  uint32_t vb16 = abcd[1U];
  uint32_t vc16 = abcd[2U];
  uint32_t vd16 = abcd[3U];
  uint8_t *b16 = x + (uint32_t)4U;
  uint32_t u15 = load32_le(b16);
  uint32_t xk15 = u15;
  uint32_t ti16 = Hacl_Hash_Core_MD5__t[16U];
  uint32_t
  v115 =
    vb16
    +
      ((va15 + ((vb16 & vd16) | (vc16 & ~vd16)) + xk15 + ti16)
      << (uint32_t)5U
      | (va15 + ((vb16 & vd16) | (vc16 & ~vd16)) + xk15 + ti16) >> (uint32_t)27U);
  abcd[0U] = v115;
  uint32_t va16 = abcd[3U];
  uint32_t vb17 = abcd[0U];
  uint32_t vc17 = abcd[1U];
  uint32_t vd17 = abcd[2U];
  uint8_t *b17 = x + (uint32_t)24U;
  uint32_t u16 = load32_le(b17);
  uint32_t xk16 = u16;
  uint32_t ti17 = Hacl_Hash_Core_MD5__t[17U];
  uint32_t
  v116 =
    vb17
    +
      ((va16 + ((vb17 & vd17) | (vc17 & ~vd17)) + xk16 + ti17)
      << (uint32_t)9U
      | (va16 + ((vb17 & vd17) | (vc17 & ~vd17)) + xk16 + ti17) >> (uint32_t)23U);
  abcd[3U] = v116;
  uint32_t va17 = abcd[2U];
  uint32_t vb18 = abcd[3U];
  uint32_t vc18 = abcd[0U];
  uint32_t vd18 = abcd[1U];
  uint8_t *b18 = x + (uint32_t)44U;
  uint32_t u17 = load32_le(b18);
  uint32_t xk17 = u17;
  uint32_t ti18 = Hacl_Hash_Core_MD5__t[18U];
  uint32_t
  v117 =
    vb18
    +
      ((va17 + ((vb18 & vd18) | (vc18 & ~vd18)) + xk17 + ti18)
      << (uint32_t)14U
      | (va17 + ((vb18 & vd18) | (vc18 & ~vd18)) + xk17 + ti18) >> (uint32_t)18U);
  abcd[2U] = v117;
  uint32_t va18 = abcd[1U];
  uint32_t vb19 = abcd[2U];
  uint32_t vc19 = abcd[3U];
  uint32_t vd19 = abcd[0U];
  uint8_t *b19 = x;
  uint32_t u18 = load32_le(b19);
  uint32_t xk18 = u18;
  uint32_t ti19 = Hacl_Hash_Core_MD5__t[19U];
  uint32_t
  v118 =
    vb19
    +
      ((va18 + ((vb19 & vd19) | (vc19 & ~vd19)) + xk18 + ti19)
      << (uint32_t)20U
      | (va18 + ((vb19 & vd19) | (vc19 & ~vd19)) + xk18 + ti19) >> (uint32_t)12U);
  abcd[1U] = v118;
  uint32_t va19 = abcd[0U];
  uint32_t vb20 = abcd[1U];
  uint32_t vc20 = abcd[2U];
  uint32_t vd20 = abcd[3U];
  uint8_t *b20 = x + (uint32_t)20U;
  uint32_t u19 = load32_le(b20);
  uint32_t xk19 = u19;
  uint32_t ti20 = Hacl_Hash_Core_MD5__t[20U];
  uint32_t
  v119 =
    vb20
    +
      ((va19 + ((vb20 & vd20) | (vc20 & ~vd20)) + xk19 + ti20)
      << (uint32_t)5U
      | (va19 + ((vb20 & vd20) | (vc20 & ~vd20)) + xk19 + ti20) >> (uint32_t)27U);
  abcd[0U] = v119;
  uint32_t va20 = abcd[3U];
  uint32_t vb21 = abcd[0U];
  uint32_t vc21 = abcd[1U];
  uint32_t vd21 = abcd[2U];
  uint8_t *b21 = x + (uint32_t)40U;
  uint32_t u20 = load32_le(b21);
  uint32_t xk20 = u20;
  uint32_t ti21 = Hacl_Hash_Core_MD5__t[21U];
  uint32_t
  v120 =
    vb21
    +
      ((va20 + ((vb21 & vd21) | (vc21 & ~vd21)) + xk20 + ti21)
      << (uint32_t)9U
      | (va20 + ((vb21 & vd21) | (vc21 & ~vd21)) + xk20 + ti21) >> (uint32_t)23U);
  abcd[3U] = v120;
  uint32_t va21 = abcd[2U];
  uint32_t vb22 = abcd[3U];
  uint32_t vc22 = abcd[0U];
  uint32_t vd22 = abcd[1U];
  uint8_t *b22 = x + (uint32_t)60U;
  uint32_t u21 = load32_le(b22);
  uint32_t xk21 = u21;
  uint32_t ti22 = Hacl_Hash_Core_MD5__t[22U];
  uint32_t
  v121 =
    vb22
    +
      ((va21 + ((vb22 & vd22) | (vc22 & ~vd22)) + xk21 + ti22)
      << (uint32_t)14U
      | (va21 + ((vb22 & vd22) | (vc22 & ~vd22)) + xk21 + ti22) >> (uint32_t)18U);
  abcd[2U] = v121;
  uint32_t va22 = abcd[1U];
  uint32_t vb23 = abcd[2U];
  uint32_t vc23 = abcd[3U];
  uint32_t vd23 = abcd[0U];
  uint8_t *b23 = x + (uint32_t)16U;
  uint32_t u22 = load32_le(b23);
  uint32_t xk22 = u22;
  uint32_t ti23 = Hacl_Hash_Core_MD5__t[23U];
  uint32_t
  v122 =
    vb23
    +
      ((va22 + ((vb23 & vd23) | (vc23 & ~vd23)) + xk22 + ti23)
      << (uint32_t)20U
      | (va22 + ((vb23 & vd23) | (vc23 & ~vd23)) + xk22 + ti23) >> (uint32_t)12U);
  abcd[1U] = v122;
  uint32_t va23 = abcd[0U];
  uint32_t vb24 = abcd[1U];
  uint32_t vc24 = abcd[2U];
  uint32_t vd24 = abcd[3U];
  uint8_t *b24 = x + (uint32_t)36U;
  uint32_t u23 = load32_le(b24);
  uint32_t xk23 = u23;
  uint32_t ti24 = Hacl_Hash_Core_MD5__t[24U];
  uint32_t
  v123 =
    vb24
    +
      ((va23 + ((vb24 & vd24) | (vc24 & ~vd24)) + xk23 + ti24)
      << (uint32_t)5U
      | (va23 + ((vb24 & vd24) | (vc24 & ~vd24)) + xk23 + ti24) >> (uint32_t)27U);
  abcd[0U] = v123;
  uint32_t va24 = abcd[3U];
  uint32_t vb25 = abcd[0U];
  uint32_t vc25 = abcd[1U];
  uint32_t vd25 = abcd[2U];
  uint8_t *b25 = x + (uint32_t)56U;
  uint32_t u24 = load32_le(b25);
  uint32_t xk24 = u24;
  uint32_t ti25 = Hacl_Hash_Core_MD5__t[25U];
  uint32_t
  v124 =
    vb25
    +
      ((va24 + ((vb25 & vd25) | (vc25 & ~vd25)) + xk24 + ti25)
      << (uint32_t)9U
      | (va24 + ((vb25 & vd25) | (vc25 & ~vd25)) + xk24 + ti25) >> (uint32_t)23U);
  abcd[3U] = v124;
  uint32_t va25 = abcd[2U];
  uint32_t vb26 = abcd[3U];
  uint32_t vc26 = abcd[0U];
  uint32_t vd26 = abcd[1U];
  uint8_t *b26 = x + (uint32_t)12U;
  uint32_t u25 = load32_le(b26);
  uint32_t xk25 = u25;
  uint32_t ti26 = Hacl_Hash_Core_MD5__t[26U];
  uint32_t
  v125 =
    vb26
    +
      ((va25 + ((vb26 & vd26) | (vc26 & ~vd26)) + xk25 + ti26)
      << (uint32_t)14U
      | (va25 + ((vb26 & vd26) | (vc26 & ~vd26)) + xk25 + ti26) >> (uint32_t)18U);
  abcd[2U] = v125;
  uint32_t va26 = abcd[1U];
  uint32_t vb27 = abcd[2U];
  uint32_t vc27 = abcd[3U];
  uint32_t vd27 = abcd[0U];
  uint8_t *b27 = x + (uint32_t)32U;
  uint32_t u26 = load32_le(b27);
  uint32_t xk26 = u26;
  uint32_t ti27 = Hacl_Hash_Core_MD5__t[27U];
  uint32_t
  v126 =
    vb27
    +
      ((va26 + ((vb27 & vd27) | (vc27 & ~vd27)) + xk26 + ti27)
      << (uint32_t)20U
      | (va26 + ((vb27 & vd27) | (vc27 & ~vd27)) + xk26 + ti27) >> (uint32_t)12U);
  abcd[1U] = v126;
  uint32_t va27 = abcd[0U];
  uint32_t vb28 = abcd[1U];
  uint32_t vc28 = abcd[2U];
  uint32_t vd28 = abcd[3U];
  uint8_t *b28 = x + (uint32_t)52U;
  uint32_t u27 = load32_le(b28);
  uint32_t xk27 = u27;
  uint32_t ti28 = Hacl_Hash_Core_MD5__t[28U];
  uint32_t
  v127 =
    vb28
    +
      ((va27 + ((vb28 & vd28) | (vc28 & ~vd28)) + xk27 + ti28)
      << (uint32_t)5U
      | (va27 + ((vb28 & vd28) | (vc28 & ~vd28)) + xk27 + ti28) >> (uint32_t)27U);
  abcd[0U] = v127;
  uint32_t va28 = abcd[3U];
  uint32_t vb29 = abcd[0U];
  uint32_t vc29 = abcd[1U];
  uint32_t vd29 = abcd[2U];
  uint8_t *b29 = x + (uint32_t)8U;
  uint32_t u28 = load32_le(b29);
  uint32_t xk28 = u28;
  uint32_t ti29 = Hacl_Hash_Core_MD5__t[29U];
  uint32_t
  v128 =
    vb29
    +
      ((va28 + ((vb29 & vd29) | (vc29 & ~vd29)) + xk28 + ti29)
      << (uint32_t)9U
      | (va28 + ((vb29 & vd29) | (vc29 & ~vd29)) + xk28 + ti29) >> (uint32_t)23U);
  abcd[3U] = v128;
  uint32_t va29 = abcd[2U];
  uint32_t vb30 = abcd[3U];
  uint32_t vc30 = abcd[0U];
  uint32_t vd30 = abcd[1U];
  uint8_t *b30 = x + (uint32_t)28U;
  uint32_t u29 = load32_le(b30);
  uint32_t xk29 = u29;
  uint32_t ti30 = Hacl_Hash_Core_MD5__t[30U];
  uint32_t
  v129 =
    vb30
    +
      ((va29 + ((vb30 & vd30) | (vc30 & ~vd30)) + xk29 + ti30)
      << (uint32_t)14U
      | (va29 + ((vb30 & vd30) | (vc30 & ~vd30)) + xk29 + ti30) >> (uint32_t)18U);
  abcd[2U] = v129;
  uint32_t va30 = abcd[1U];
  uint32_t vb31 = abcd[2U];
  uint32_t vc31 = abcd[3U];
  uint32_t vd31 = abcd[0U];
  uint8_t *b31 = x + (uint32_t)48U;
  uint32_t u30 = load32_le(b31);
  uint32_t xk30 = u30;
  uint32_t ti31 = Hacl_Hash_Core_MD5__t[31U];
  uint32_t
  v130 =
    vb31
    +
      ((va30 + ((vb31 & vd31) | (vc31 & ~vd31)) + xk30 + ti31)
      << (uint32_t)20U
      | (va30 + ((vb31 & vd31) | (vc31 & ~vd31)) + xk30 + ti31) >> (uint32_t)12U);
  abcd[1U] = v130;
  uint32_t va31 = abcd[0U];
  uint32_t vb32 = abcd[1U];
  uint32_t vc32 = abcd[2U];
  uint32_t vd32 = abcd[3U];
  uint8_t *b32 = x + (uint32_t)20U;
  uint32_t u31 = load32_le(b32);
  uint32_t xk31 = u31;
  uint32_t ti32 = Hacl_Hash_Core_MD5__t[32U];
  uint32_t
  v131 =
    vb32
    +
      ((va31 + (vb32 ^ (vc32 ^ vd32)) + xk31 + ti32)
      << (uint32_t)4U
      | (va31 + (vb32 ^ (vc32 ^ vd32)) + xk31 + ti32) >> (uint32_t)28U);
  abcd[0U] = v131;
  uint32_t va32 = abcd[3U];
  uint32_t vb33 = abcd[0U];
  uint32_t vc33 = abcd[1U];
  uint32_t vd33 = abcd[2U];
  uint8_t *b33 = x + (uint32_t)32U;
  uint32_t u32 = load32_le(b33);
  uint32_t xk32 = u32;
  uint32_t ti33 = Hacl_Hash_Core_MD5__t[33U];
  uint32_t
  v132 =
    vb33
    +
      ((va32 + (vb33 ^ (vc33 ^ vd33)) + xk32 + ti33)
      << (uint32_t)11U
      | (va32 + (vb33 ^ (vc33 ^ vd33)) + xk32 + ti33) >> (uint32_t)21U);
  abcd[3U] = v132;
  uint32_t va33 = abcd[2U];
  uint32_t vb34 = abcd[3U];
  uint32_t vc34 = abcd[0U];
  uint32_t vd34 = abcd[1U];
  uint8_t *b34 = x + (uint32_t)44U;
  uint32_t u33 = load32_le(b34);
  uint32_t xk33 = u33;
  uint32_t ti34 = Hacl_Hash_Core_MD5__t[34U];
  uint32_t
  v133 =
    vb34
    +
      ((va33 + (vb34 ^ (vc34 ^ vd34)) + xk33 + ti34)
      << (uint32_t)16U
      | (va33 + (vb34 ^ (vc34 ^ vd34)) + xk33 + ti34) >> (uint32_t)16U);
  abcd[2U] = v133;
  uint32_t va34 = abcd[1U];
  uint32_t vb35 = abcd[2U];
  uint32_t vc35 = abcd[3U];
  uint32_t vd35 = abcd[0U];
  uint8_t *b35 = x + (uint32_t)56U;
  uint32_t u34 = load32_le(b35);
  uint32_t xk34 = u34;
  uint32_t ti35 = Hacl_Hash_Core_MD5__t[35U];
  uint32_t
  v134 =
    vb35
    +
      ((va34 + (vb35 ^ (vc35 ^ vd35)) + xk34 + ti35)
      << (uint32_t)23U
      | (va34 + (vb35 ^ (vc35 ^ vd35)) + xk34 + ti35) >> (uint32_t)9U);
  abcd[1U] = v134;
  uint32_t va35 = abcd[0U];
  uint32_t vb36 = abcd[1U];
  uint32_t vc36 = abcd[2U];
  uint32_t vd36 = abcd[3U];
  uint8_t *b36 = x + (uint32_t)4U;
  uint32_t u35 = load32_le(b36);
  uint32_t xk35 = u35;
  uint32_t ti36 = Hacl_Hash_Core_MD5__t[36U];
  uint32_t
  v135 =
    vb36
    +
      ((va35 + (vb36 ^ (vc36 ^ vd36)) + xk35 + ti36)
      << (uint32_t)4U
      | (va35 + (vb36 ^ (vc36 ^ vd36)) + xk35 + ti36) >> (uint32_t)28U);
  abcd[0U] = v135;
  uint32_t va36 = abcd[3U];
  uint32_t vb37 = abcd[0U];
  uint32_t vc37 = abcd[1U];
  uint32_t vd37 = abcd[2U];
  uint8_t *b37 = x + (uint32_t)16U;
  uint32_t u36 = load32_le(b37);
  uint32_t xk36 = u36;
  uint32_t ti37 = Hacl_Hash_Core_MD5__t[37U];
  uint32_t
  v136 =
    vb37
    +
      ((va36 + (vb37 ^ (vc37 ^ vd37)) + xk36 + ti37)
      << (uint32_t)11U
      | (va36 + (vb37 ^ (vc37 ^ vd37)) + xk36 + ti37) >> (uint32_t)21U);
  abcd[3U] = v136;
  uint32_t va37 = abcd[2U];
  uint32_t vb38 = abcd[3U];
  uint32_t vc38 = abcd[0U];
  uint32_t vd38 = abcd[1U];
  uint8_t *b38 = x + (uint32_t)28U;
  uint32_t u37 = load32_le(b38);
  uint32_t xk37 = u37;
  uint32_t ti38 = Hacl_Hash_Core_MD5__t[38U];
  uint32_t
  v137 =
    vb38
    +
      ((va37 + (vb38 ^ (vc38 ^ vd38)) + xk37 + ti38)
      << (uint32_t)16U
      | (va37 + (vb38 ^ (vc38 ^ vd38)) + xk37 + ti38) >> (uint32_t)16U);
  abcd[2U] = v137;
  uint32_t va38 = abcd[1U];
  uint32_t vb39 = abcd[2U];
  uint32_t vc39 = abcd[3U];
  uint32_t vd39 = abcd[0U];
  uint8_t *b39 = x + (uint32_t)40U;
  uint32_t u38 = load32_le(b39);
  uint32_t xk38 = u38;
  uint32_t ti39 = Hacl_Hash_Core_MD5__t[39U];
  uint32_t
  v138 =
    vb39
    +
      ((va38 + (vb39 ^ (vc39 ^ vd39)) + xk38 + ti39)
      << (uint32_t)23U
      | (va38 + (vb39 ^ (vc39 ^ vd39)) + xk38 + ti39) >> (uint32_t)9U);
  abcd[1U] = v138;
  uint32_t va39 = abcd[0U];
  uint32_t vb40 = abcd[1U];
  uint32_t vc40 = abcd[2U];
  uint32_t vd40 = abcd[3U];
  uint8_t *b40 = x + (uint32_t)52U;
  uint32_t u39 = load32_le(b40);
  uint32_t xk39 = u39;
  uint32_t ti40 = Hacl_Hash_Core_MD5__t[40U];
  uint32_t
  v139 =
    vb40
    +
      ((va39 + (vb40 ^ (vc40 ^ vd40)) + xk39 + ti40)
      << (uint32_t)4U
      | (va39 + (vb40 ^ (vc40 ^ vd40)) + xk39 + ti40) >> (uint32_t)28U);
  abcd[0U] = v139;
  uint32_t va40 = abcd[3U];
  uint32_t vb41 = abcd[0U];
  uint32_t vc41 = abcd[1U];
  uint32_t vd41 = abcd[2U];
  uint8_t *b41 = x;
  uint32_t u40 = load32_le(b41);
  uint32_t xk40 = u40;
  uint32_t ti41 = Hacl_Hash_Core_MD5__t[41U];
  uint32_t
  v140 =
    vb41
    +
      ((va40 + (vb41 ^ (vc41 ^ vd41)) + xk40 + ti41)
      << (uint32_t)11U
      | (va40 + (vb41 ^ (vc41 ^ vd41)) + xk40 + ti41) >> (uint32_t)21U);
  abcd[3U] = v140;
  uint32_t va41 = abcd[2U];
  uint32_t vb42 = abcd[3U];
  uint32_t vc42 = abcd[0U];
  uint32_t vd42 = abcd[1U];
  uint8_t *b42 = x + (uint32_t)12U;
  uint32_t u41 = load32_le(b42);
  uint32_t xk41 = u41;
  uint32_t ti42 = Hacl_Hash_Core_MD5__t[42U];
  uint32_t
  v141 =
    vb42
    +
      ((va41 + (vb42 ^ (vc42 ^ vd42)) + xk41 + ti42)
      << (uint32_t)16U
      | (va41 + (vb42 ^ (vc42 ^ vd42)) + xk41 + ti42) >> (uint32_t)16U);
  abcd[2U] = v141;
  uint32_t va42 = abcd[1U];
  uint32_t vb43 = abcd[2U];
  uint32_t vc43 = abcd[3U];
  uint32_t vd43 = abcd[0U];
  uint8_t *b43 = x + (uint32_t)24U;
  uint32_t u42 = load32_le(b43);
  uint32_t xk42 = u42;
  uint32_t ti43 = Hacl_Hash_Core_MD5__t[43U];
  uint32_t
  v142 =
    vb43
    +
      ((va42 + (vb43 ^ (vc43 ^ vd43)) + xk42 + ti43)
      << (uint32_t)23U
      | (va42 + (vb43 ^ (vc43 ^ vd43)) + xk42 + ti43) >> (uint32_t)9U);
  abcd[1U] = v142;
  uint32_t va43 = abcd[0U];
  uint32_t vb44 = abcd[1U];
  uint32_t vc44 = abcd[2U];
  uint32_t vd44 = abcd[3U];
  uint8_t *b44 = x + (uint32_t)36U;
  uint32_t u43 = load32_le(b44);
  uint32_t xk43 = u43;
  uint32_t ti44 = Hacl_Hash_Core_MD5__t[44U];
  uint32_t
  v143 =
    vb44
    +
      ((va43 + (vb44 ^ (vc44 ^ vd44)) + xk43 + ti44)
      << (uint32_t)4U
      | (va43 + (vb44 ^ (vc44 ^ vd44)) + xk43 + ti44) >> (uint32_t)28U);
  abcd[0U] = v143;
  uint32_t va44 = abcd[3U];
  uint32_t vb45 = abcd[0U];
  uint32_t vc45 = abcd[1U];
  uint32_t vd45 = abcd[2U];
  uint8_t *b45 = x + (uint32_t)48U;
  uint32_t u44 = load32_le(b45);
  uint32_t xk44 = u44;
  uint32_t ti45 = Hacl_Hash_Core_MD5__t[45U];
  uint32_t
  v144 =
    vb45
    +
      ((va44 + (vb45 ^ (vc45 ^ vd45)) + xk44 + ti45)
      << (uint32_t)11U
      | (va44 + (vb45 ^ (vc45 ^ vd45)) + xk44 + ti45) >> (uint32_t)21U);
  abcd[3U] = v144;
  uint32_t va45 = abcd[2U];
  uint32_t vb46 = abcd[3U];
  uint32_t vc46 = abcd[0U];
  uint32_t vd46 = abcd[1U];
  uint8_t *b46 = x + (uint32_t)60U;
  uint32_t u45 = load32_le(b46);
  uint32_t xk45 = u45;
  uint32_t ti46 = Hacl_Hash_Core_MD5__t[46U];
  uint32_t
  v145 =
    vb46
    +
      ((va45 + (vb46 ^ (vc46 ^ vd46)) + xk45 + ti46)
      << (uint32_t)16U
      | (va45 + (vb46 ^ (vc46 ^ vd46)) + xk45 + ti46) >> (uint32_t)16U);
  abcd[2U] = v145;
  uint32_t va46 = abcd[1U];
  uint32_t vb47 = abcd[2U];
  uint32_t vc47 = abcd[3U];
  uint32_t vd47 = abcd[0U];
  uint8_t *b47 = x + (uint32_t)8U;
  uint32_t u46 = load32_le(b47);
  uint32_t xk46 = u46;
  uint32_t ti47 = Hacl_Hash_Core_MD5__t[47U];
  uint32_t
  v146 =
    vb47
    +
      ((va46 + (vb47 ^ (vc47 ^ vd47)) + xk46 + ti47)
      << (uint32_t)23U
      | (va46 + (vb47 ^ (vc47 ^ vd47)) + xk46 + ti47) >> (uint32_t)9U);
  abcd[1U] = v146;
  uint32_t va47 = abcd[0U];
  uint32_t vb48 = abcd[1U];
  uint32_t vc48 = abcd[2U];
  uint32_t vd48 = abcd[3U];
  uint8_t *b48 = x;
  uint32_t u47 = load32_le(b48);
  uint32_t xk47 = u47;
  uint32_t ti48 = Hacl_Hash_Core_MD5__t[48U];
  uint32_t
  v147 =
    vb48
    +
      ((va47 + (vc48 ^ (vb48 | ~vd48)) + xk47 + ti48)
      << (uint32_t)6U
      | (va47 + (vc48 ^ (vb48 | ~vd48)) + xk47 + ti48) >> (uint32_t)26U);
  abcd[0U] = v147;
  uint32_t va48 = abcd[3U];
  uint32_t vb49 = abcd[0U];
  uint32_t vc49 = abcd[1U];
  uint32_t vd49 = abcd[2U];
  uint8_t *b49 = x + (uint32_t)28U;
  uint32_t u48 = load32_le(b49);
  uint32_t xk48 = u48;
  uint32_t ti49 = Hacl_Hash_Core_MD5__t[49U];
  uint32_t
  v148 =
    vb49
    +
      ((va48 + (vc49 ^ (vb49 | ~vd49)) + xk48 + ti49)
      << (uint32_t)10U
      | (va48 + (vc49 ^ (vb49 | ~vd49)) + xk48 + ti49) >> (uint32_t)22U);
  abcd[3U] = v148;
  uint32_t va49 = abcd[2U];
  uint32_t vb50 = abcd[3U];
  uint32_t vc50 = abcd[0U];
  uint32_t vd50 = abcd[1U];
  uint8_t *b50 = x + (uint32_t)56U;
  uint32_t u49 = load32_le(b50);
  uint32_t xk49 = u49;
  uint32_t ti50 = Hacl_Hash_Core_MD5__t[50U];
  uint32_t
  v149 =
    vb50
    +
      ((va49 + (vc50 ^ (vb50 | ~vd50)) + xk49 + ti50)
      << (uint32_t)15U
      | (va49 + (vc50 ^ (vb50 | ~vd50)) + xk49 + ti50) >> (uint32_t)17U);
  abcd[2U] = v149;
  uint32_t va50 = abcd[1U];
  uint32_t vb51 = abcd[2U];
  uint32_t vc51 = abcd[3U];
  uint32_t vd51 = abcd[0U];
  uint8_t *b51 = x + (uint32_t)20U;
  uint32_t u50 = load32_le(b51);
  uint32_t xk50 = u50;
  uint32_t ti51 = Hacl_Hash_Core_MD5__t[51U];
  uint32_t
  v150 =
    vb51
    +
      ((va50 + (vc51 ^ (vb51 | ~vd51)) + xk50 + ti51)
      << (uint32_t)21U
      | (va50 + (vc51 ^ (vb51 | ~vd51)) + xk50 + ti51) >> (uint32_t)11U);
  abcd[1U] = v150;
  uint32_t va51 = abcd[0U];
  uint32_t vb52 = abcd[1U];
  uint32_t vc52 = abcd[2U];
  uint32_t vd52 = abcd[3U];
  uint8_t *b52 = x + (uint32_t)48U;
  uint32_t u51 = load32_le(b52);
  uint32_t xk51 = u51;
  uint32_t ti52 = Hacl_Hash_Core_MD5__t[52U];
  uint32_t
  v151 =
    vb52
    +
      ((va51 + (vc52 ^ (vb52 | ~vd52)) + xk51 + ti52)
      << (uint32_t)6U
      | (va51 + (vc52 ^ (vb52 | ~vd52)) + xk51 + ti52) >> (uint32_t)26U);
  abcd[0U] = v151;
  uint32_t va52 = abcd[3U];
  uint32_t vb53 = abcd[0U];
  uint32_t vc53 = abcd[1U];
  uint32_t vd53 = abcd[2U];
  uint8_t *b53 = x + (uint32_t)12U;
  uint32_t u52 = load32_le(b53);
  uint32_t xk52 = u52;
  uint32_t ti53 = Hacl_Hash_Core_MD5__t[53U];
  uint32_t
  v152 =
    vb53
    +
      ((va52 + (vc53 ^ (vb53 | ~vd53)) + xk52 + ti53)
      << (uint32_t)10U
      | (va52 + (vc53 ^ (vb53 | ~vd53)) + xk52 + ti53) >> (uint32_t)22U);
  abcd[3U] = v152;
  uint32_t va53 = abcd[2U];
  uint32_t vb54 = abcd[3U];
  uint32_t vc54 = abcd[0U];
  uint32_t vd54 = abcd[1U];
  uint8_t *b54 = x + (uint32_t)40U;
  uint32_t u53 = load32_le(b54);
  uint32_t xk53 = u53;
  uint32_t ti54 = Hacl_Hash_Core_MD5__t[54U];
  uint32_t
  v153 =
    vb54
    +
      ((va53 + (vc54 ^ (vb54 | ~vd54)) + xk53 + ti54)
      << (uint32_t)15U
      | (va53 + (vc54 ^ (vb54 | ~vd54)) + xk53 + ti54) >> (uint32_t)17U);
  abcd[2U] = v153;
  uint32_t va54 = abcd[1U];
  uint32_t vb55 = abcd[2U];
  uint32_t vc55 = abcd[3U];
  uint32_t vd55 = abcd[0U];
  uint8_t *b55 = x + (uint32_t)4U;
  uint32_t u54 = load32_le(b55);
  uint32_t xk54 = u54;
  uint32_t ti55 = Hacl_Hash_Core_MD5__t[55U];
  uint32_t
  v154 =
    vb55
    +
      ((va54 + (vc55 ^ (vb55 | ~vd55)) + xk54 + ti55)
      << (uint32_t)21U
      | (va54 + (vc55 ^ (vb55 | ~vd55)) + xk54 + ti55) >> (uint32_t)11U);
  abcd[1U] = v154;
  uint32_t va55 = abcd[0U];
  uint32_t vb56 = abcd[1U];
  uint32_t vc56 = abcd[2U];
  uint32_t vd56 = abcd[3U];
  uint8_t *b56 = x + (uint32_t)32U;
  uint32_t u55 = load32_le(b56);
  uint32_t xk55 = u55;
  uint32_t ti56 = Hacl_Hash_Core_MD5__t[56U];
  uint32_t
  v155 =
    vb56
    +
      ((va55 + (vc56 ^ (vb56 | ~vd56)) + xk55 + ti56)
      << (uint32_t)6U
      | (va55 + (vc56 ^ (vb56 | ~vd56)) + xk55 + ti56) >> (uint32_t)26U);
  abcd[0U] = v155;
  uint32_t va56 = abcd[3U];
  uint32_t vb57 = abcd[0U];
  uint32_t vc57 = abcd[1U];
  uint32_t vd57 = abcd[2U];
  uint8_t *b57 = x + (uint32_t)60U;
  uint32_t u56 = load32_le(b57);
  uint32_t xk56 = u56;
  uint32_t ti57 = Hacl_Hash_Core_MD5__t[57U];
  uint32_t
  v156 =
    vb57
    +
      ((va56 + (vc57 ^ (vb57 | ~vd57)) + xk56 + ti57)
      << (uint32_t)10U
      | (va56 + (vc57 ^ (vb57 | ~vd57)) + xk56 + ti57) >> (uint32_t)22U);
  abcd[3U] = v156;
  uint32_t va57 = abcd[2U];
  uint32_t vb58 = abcd[3U];
  uint32_t vc58 = abcd[0U];
  uint32_t vd58 = abcd[1U];
  uint8_t *b58 = x + (uint32_t)24U;
  uint32_t u57 = load32_le(b58);
  uint32_t xk57 = u57;
  uint32_t ti58 = Hacl_Hash_Core_MD5__t[58U];
  uint32_t
  v157 =
    vb58
    +
      ((va57 + (vc58 ^ (vb58 | ~vd58)) + xk57 + ti58)
      << (uint32_t)15U
      | (va57 + (vc58 ^ (vb58 | ~vd58)) + xk57 + ti58) >> (uint32_t)17U);
  abcd[2U] = v157;
  uint32_t va58 = abcd[1U];
  uint32_t vb59 = abcd[2U];
  uint32_t vc59 = abcd[3U];
  uint32_t vd59 = abcd[0U];
  uint8_t *b59 = x + (uint32_t)52U;
  uint32_t u58 = load32_le(b59);
  uint32_t xk58 = u58;
  uint32_t ti59 = Hacl_Hash_Core_MD5__t[59U];
  uint32_t
  v158 =
    vb59
    +
      ((va58 + (vc59 ^ (vb59 | ~vd59)) + xk58 + ti59)
      << (uint32_t)21U
      | (va58 + (vc59 ^ (vb59 | ~vd59)) + xk58 + ti59) >> (uint32_t)11U);
  abcd[1U] = v158;
  uint32_t va59 = abcd[0U];
  uint32_t vb60 = abcd[1U];
  uint32_t vc60 = abcd[2U];
  uint32_t vd60 = abcd[3U];
  uint8_t *b60 = x + (uint32_t)16U;
  uint32_t u59 = load32_le(b60);
  uint32_t xk59 = u59;
  uint32_t ti60 = Hacl_Hash_Core_MD5__t[60U];
  uint32_t
  v159 =
    vb60
    +
      ((va59 + (vc60 ^ (vb60 | ~vd60)) + xk59 + ti60)
      << (uint32_t)6U
      | (va59 + (vc60 ^ (vb60 | ~vd60)) + xk59 + ti60) >> (uint32_t)26U);
  abcd[0U] = v159;
  uint32_t va60 = abcd[3U];
  uint32_t vb61 = abcd[0U];
  uint32_t vc61 = abcd[1U];
  uint32_t vd61 = abcd[2U];
  uint8_t *b61 = x + (uint32_t)44U;
  uint32_t u60 = load32_le(b61);
  uint32_t xk60 = u60;
  uint32_t ti61 = Hacl_Hash_Core_MD5__t[61U];
  uint32_t
  v160 =
    vb61
    +
      ((va60 + (vc61 ^ (vb61 | ~vd61)) + xk60 + ti61)
      << (uint32_t)10U
      | (va60 + (vc61 ^ (vb61 | ~vd61)) + xk60 + ti61) >> (uint32_t)22U);
  abcd[3U] = v160;
  uint32_t va61 = abcd[2U];
  uint32_t vb62 = abcd[3U];
  uint32_t vc62 = abcd[0U];
  uint32_t vd62 = abcd[1U];
  uint8_t *b62 = x + (uint32_t)8U;
  uint32_t u61 = load32_le(b62);
  uint32_t xk61 = u61;
  uint32_t ti62 = Hacl_Hash_Core_MD5__t[62U];
  uint32_t
  v161 =
    vb62
    +
      ((va61 + (vc62 ^ (vb62 | ~vd62)) + xk61 + ti62)
      << (uint32_t)15U
      | (va61 + (vc62 ^ (vb62 | ~vd62)) + xk61 + ti62) >> (uint32_t)17U);
  abcd[2U] = v161;
  uint32_t va62 = abcd[1U];
  uint32_t vb = abcd[2U];
  uint32_t vc = abcd[3U];
  uint32_t vd = abcd[0U];
  uint8_t *b63 = x + (uint32_t)36U;
  uint32_t u62 = load32_le(b63);
  uint32_t xk62 = u62;
  uint32_t ti = Hacl_Hash_Core_MD5__t[63U];
  uint32_t
  v162 =
    vb
    +
      ((va62 + (vc ^ (vb | ~vd)) + xk62 + ti)
      << (uint32_t)21U
      | (va62 + (vc ^ (vb | ~vd)) + xk62 + ti) >> (uint32_t)11U);
  abcd[1U] = v162;
  uint32_t a = abcd[0U];
  uint32_t b = abcd[1U];
  uint32_t c = abcd[2U];
  uint32_t d = abcd[3U];
  abcd[0U] = a + aa;
  abcd[1U] = b + bb;
  abcd[2U] = c + cc;
  abcd[3U] = d + dd;
}

void Hacl_Hash_Core_MD5_legacy_pad(uint64_t len, uint8_t *dst)
{
  uint8_t *dst1 = dst;
  dst1[0U] = (uint8_t)0x80U;
  uint8_t *dst2 = dst + (uint32_t)1U;
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    < ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(len % (uint64_t)(uint32_t)64U))) % (uint32_t)64U;
    i = i + (uint32_t)1U)
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
  store64_le(dst3, len << (uint32_t)3U);
}

void Hacl_Hash_Core_MD5_legacy_finish(uint32_t *s, uint8_t *dst)
{
  uint32_t *uu____0 = s;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
  {
    store32_le(dst + i * (uint32_t)4U, uu____0[i]);
  }
}

void Hacl_Hash_SHA1_legacy_update_multi(uint32_t *s, uint8_t *blocks, uint32_t n_blocks)
{
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i = i + (uint32_t)1U)
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
  pad_len1 =
    (uint32_t)1U
    +
      ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(total_input_len % (uint64_t)(uint32_t)64U)))
      % (uint32_t)64U
    + (uint32_t)8U;
  uint32_t tmp_len = rest_len + pad_len1;
  uint8_t tmp_twoblocks[128U] = { 0U };
  uint8_t *tmp = tmp_twoblocks;
  uint8_t *tmp_rest = tmp;
  uint8_t *tmp_pad = tmp + rest_len;
  memcpy(tmp_rest, rest, rest_len * sizeof rest[0U]);
  Hacl_Hash_Core_SHA1_legacy_pad(total_input_len, tmp_pad);
  Hacl_Hash_SHA1_legacy_update_multi(s, tmp, tmp_len / (uint32_t)64U);
}

void Hacl_Hash_SHA1_legacy_hash(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint32_t
  s[5U] =
    {
      (uint32_t)0x67452301U, (uint32_t)0xefcdab89U, (uint32_t)0x98badcfeU, (uint32_t)0x10325476U,
      (uint32_t)0xc3d2e1f0U
    };
  uint32_t blocks_n = input_len / (uint32_t)64U;
  uint32_t blocks_len = blocks_n * (uint32_t)64U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  Hacl_Hash_SHA1_legacy_update_multi(s, blocks, blocks_n);
  Hacl_Hash_SHA1_legacy_update_last(s, (uint64_t)blocks_len, rest, rest_len);
  Hacl_Hash_Core_SHA1_legacy_finish(s, dst);
}

static uint32_t
Hacl_Hash_Core_SHA1__h0[5U] =
  {
    (uint32_t)0x67452301U, (uint32_t)0xefcdab89U, (uint32_t)0x98badcfeU, (uint32_t)0x10325476U,
    (uint32_t)0xc3d2e1f0U
  };

void Hacl_Hash_Core_SHA1_legacy_init(uint32_t *s)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)5U; i = i + (uint32_t)1U)
  {
    s[i] = Hacl_Hash_Core_SHA1__h0[i];
  }
}

void Hacl_Hash_Core_SHA1_legacy_update(uint32_t *h, uint8_t *l)
{
  uint32_t ha = h[0U];
  uint32_t hb = h[1U];
  uint32_t hc = h[2U];
  uint32_t hd1 = h[3U];
  uint32_t he = h[4U];
  uint32_t _w[80U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)80U; i = i + (uint32_t)1U)
  {
    uint32_t v1;
    if (i < (uint32_t)16U)
    {
      uint8_t *b = l + i * (uint32_t)4U;
      uint32_t u = load32_be(b);
      v1 = u;
    }
    else
    {
      uint32_t wmit3 = _w[i - (uint32_t)3U];
      uint32_t wmit8 = _w[i - (uint32_t)8U];
      uint32_t wmit14 = _w[i - (uint32_t)14U];
      uint32_t wmit16 = _w[i - (uint32_t)16U];
      v1 =
        (wmit3 ^ (wmit8 ^ (wmit14 ^ wmit16)))
        << (uint32_t)1U
        | (wmit3 ^ (wmit8 ^ (wmit14 ^ wmit16))) >> (uint32_t)31U;
    }
    _w[i] = v1;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)80U; i = i + (uint32_t)1U)
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
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)80U; i = i + (uint32_t)1U)
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
  h[3U] = std + hd1;
  h[4U] = ste + he;
}

void Hacl_Hash_Core_SHA1_legacy_pad(uint64_t len, uint8_t *dst)
{
  uint8_t *dst1 = dst;
  dst1[0U] = (uint8_t)0x80U;
  uint8_t *dst2 = dst + (uint32_t)1U;
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    < ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(len % (uint64_t)(uint32_t)64U))) % (uint32_t)64U;
    i = i + (uint32_t)1U)
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
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)5U; i = i + (uint32_t)1U)
  {
    store32_be(dst + i * (uint32_t)4U, uu____0[i]);
  }
}

void Hacl_Hash_SHA2_update_multi_224(uint32_t *s, uint8_t *blocks, uint32_t n_blocks)
{
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i = i + (uint32_t)1U)
  {
    uint32_t sz = (uint32_t)64U;
    uint8_t *block = blocks + sz * i;
    Hacl_Hash_Core_SHA2_update_224(s, block);
  }
}

void Hacl_Hash_SHA2_update_multi_256(uint32_t *s, uint8_t *blocks, uint32_t n_blocks)
{
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i = i + (uint32_t)1U)
  {
    uint32_t sz = (uint32_t)64U;
    uint8_t *block = blocks + sz * i;
    Hacl_Hash_Core_SHA2_update_256(s, block);
  }
}

void Hacl_Hash_SHA2_update_multi_384(uint64_t *s, uint8_t *blocks, uint32_t n_blocks)
{
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i = i + (uint32_t)1U)
  {
    uint32_t sz = (uint32_t)128U;
    uint8_t *block = blocks + sz * i;
    Hacl_Hash_Core_SHA2_update_384(s, block);
  }
}

void Hacl_Hash_SHA2_update_multi_512(uint64_t *s, uint8_t *blocks, uint32_t n_blocks)
{
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i = i + (uint32_t)1U)
  {
    uint32_t sz = (uint32_t)128U;
    uint8_t *block = blocks + sz * i;
    Hacl_Hash_Core_SHA2_update_512(s, block);
  }
}

void
Hacl_Hash_SHA2_update_last_224(
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
  Hacl_Hash_SHA2_update_multi_224(s, blocks, blocks_n);
  uint64_t total_input_len = prev_len + (uint64_t)input_len;
  uint32_t
  pad_len1 =
    (uint32_t)1U
    +
      ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(total_input_len % (uint64_t)(uint32_t)64U)))
      % (uint32_t)64U
    + (uint32_t)8U;
  uint32_t tmp_len = rest_len + pad_len1;
  uint8_t tmp_twoblocks[128U] = { 0U };
  uint8_t *tmp = tmp_twoblocks;
  uint8_t *tmp_rest = tmp;
  uint8_t *tmp_pad = tmp + rest_len;
  memcpy(tmp_rest, rest, rest_len * sizeof rest[0U]);
  Hacl_Hash_Core_SHA2_pad_224(total_input_len, tmp_pad);
  Hacl_Hash_SHA2_update_multi_224(s, tmp, tmp_len / (uint32_t)64U);
}

void
Hacl_Hash_SHA2_update_last_256(
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
  Hacl_Hash_SHA2_update_multi_256(s, blocks, blocks_n);
  uint64_t total_input_len = prev_len + (uint64_t)input_len;
  uint32_t
  pad_len1 =
    (uint32_t)1U
    +
      ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(total_input_len % (uint64_t)(uint32_t)64U)))
      % (uint32_t)64U
    + (uint32_t)8U;
  uint32_t tmp_len = rest_len + pad_len1;
  uint8_t tmp_twoblocks[128U] = { 0U };
  uint8_t *tmp = tmp_twoblocks;
  uint8_t *tmp_rest = tmp;
  uint8_t *tmp_pad = tmp + rest_len;
  memcpy(tmp_rest, rest, rest_len * sizeof rest[0U]);
  Hacl_Hash_Core_SHA2_pad_256(total_input_len, tmp_pad);
  Hacl_Hash_SHA2_update_multi_256(s, tmp, tmp_len / (uint32_t)64U);
}

void
Hacl_Hash_SHA2_update_last_384(
  uint64_t *s,
  uint128_t prev_len,
  uint8_t *input,
  uint32_t input_len
)
{
  uint32_t blocks_n = input_len / (uint32_t)128U;
  uint32_t blocks_len = blocks_n * (uint32_t)128U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  Hacl_Hash_SHA2_update_multi_384(s, blocks, blocks_n);
  uint128_t total_input_len = prev_len + (uint128_t)(uint64_t)input_len;
  uint32_t
  pad_len1 =
    (uint32_t)1U
    +
      ((uint32_t)256U
      - ((uint32_t)17U + (uint32_t)((uint64_t)total_input_len % (uint64_t)(uint32_t)128U)))
      % (uint32_t)128U
    + (uint32_t)16U;
  uint32_t tmp_len = rest_len + pad_len1;
  uint8_t tmp_twoblocks[256U] = { 0U };
  uint8_t *tmp = tmp_twoblocks;
  uint8_t *tmp_rest = tmp;
  uint8_t *tmp_pad = tmp + rest_len;
  memcpy(tmp_rest, rest, rest_len * sizeof rest[0U]);
  Hacl_Hash_Core_SHA2_pad_384(total_input_len, tmp_pad);
  Hacl_Hash_SHA2_update_multi_384(s, tmp, tmp_len / (uint32_t)128U);
}

void
Hacl_Hash_SHA2_update_last_512(
  uint64_t *s,
  uint128_t prev_len,
  uint8_t *input,
  uint32_t input_len
)
{
  uint32_t blocks_n = input_len / (uint32_t)128U;
  uint32_t blocks_len = blocks_n * (uint32_t)128U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  Hacl_Hash_SHA2_update_multi_512(s, blocks, blocks_n);
  uint128_t total_input_len = prev_len + (uint128_t)(uint64_t)input_len;
  uint32_t
  pad_len1 =
    (uint32_t)1U
    +
      ((uint32_t)256U
      - ((uint32_t)17U + (uint32_t)((uint64_t)total_input_len % (uint64_t)(uint32_t)128U)))
      % (uint32_t)128U
    + (uint32_t)16U;
  uint32_t tmp_len = rest_len + pad_len1;
  uint8_t tmp_twoblocks[256U] = { 0U };
  uint8_t *tmp = tmp_twoblocks;
  uint8_t *tmp_rest = tmp;
  uint8_t *tmp_pad = tmp + rest_len;
  memcpy(tmp_rest, rest, rest_len * sizeof rest[0U]);
  Hacl_Hash_Core_SHA2_pad_512(total_input_len, tmp_pad);
  Hacl_Hash_SHA2_update_multi_512(s, tmp, tmp_len / (uint32_t)128U);
}

void Hacl_Hash_SHA2_hash_224(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint32_t
  s[8U] =
    {
      (uint32_t)0xc1059ed8U, (uint32_t)0x367cd507U, (uint32_t)0x3070dd17U, (uint32_t)0xf70e5939U,
      (uint32_t)0xffc00b31U, (uint32_t)0x68581511U, (uint32_t)0x64f98fa7U, (uint32_t)0xbefa4fa4U
    };
  uint32_t blocks_n = input_len / (uint32_t)64U;
  uint32_t blocks_len = blocks_n * (uint32_t)64U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  Hacl_Hash_SHA2_update_multi_224(s, blocks, blocks_n);
  Hacl_Hash_SHA2_update_last_224(s, (uint64_t)blocks_len, rest, rest_len);
  Hacl_Hash_Core_SHA2_finish_224(s, dst);
}

void Hacl_Hash_SHA2_hash_256(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint32_t
  s[8U] =
    {
      (uint32_t)0x6a09e667U, (uint32_t)0xbb67ae85U, (uint32_t)0x3c6ef372U, (uint32_t)0xa54ff53aU,
      (uint32_t)0x510e527fU, (uint32_t)0x9b05688cU, (uint32_t)0x1f83d9abU, (uint32_t)0x5be0cd19U
    };
  uint32_t blocks_n = input_len / (uint32_t)64U;
  uint32_t blocks_len = blocks_n * (uint32_t)64U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  Hacl_Hash_SHA2_update_multi_256(s, blocks, blocks_n);
  Hacl_Hash_SHA2_update_last_256(s, (uint64_t)blocks_len, rest, rest_len);
  Hacl_Hash_Core_SHA2_finish_256(s, dst);
}

void Hacl_Hash_SHA2_hash_384(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint64_t
  s[8U] =
    {
      (uint64_t)0xcbbb9d5dc1059ed8U, (uint64_t)0x629a292a367cd507U, (uint64_t)0x9159015a3070dd17U,
      (uint64_t)0x152fecd8f70e5939U, (uint64_t)0x67332667ffc00b31U, (uint64_t)0x8eb44a8768581511U,
      (uint64_t)0xdb0c2e0d64f98fa7U, (uint64_t)0x47b5481dbefa4fa4U
    };
  uint32_t blocks_n = input_len / (uint32_t)128U;
  uint32_t blocks_len = blocks_n * (uint32_t)128U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  Hacl_Hash_SHA2_update_multi_384(s, blocks, blocks_n);
  Hacl_Hash_SHA2_update_last_384(s, (uint128_t)(uint64_t)blocks_len, rest, rest_len);
  Hacl_Hash_Core_SHA2_finish_384(s, dst);
}

void Hacl_Hash_SHA2_hash_512(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint64_t
  s[8U] =
    {
      (uint64_t)0x6a09e667f3bcc908U, (uint64_t)0xbb67ae8584caa73bU, (uint64_t)0x3c6ef372fe94f82bU,
      (uint64_t)0xa54ff53a5f1d36f1U, (uint64_t)0x510e527fade682d1U, (uint64_t)0x9b05688c2b3e6c1fU,
      (uint64_t)0x1f83d9abfb41bd6bU, (uint64_t)0x5be0cd19137e2179U
    };
  uint32_t blocks_n = input_len / (uint32_t)128U;
  uint32_t blocks_len = blocks_n * (uint32_t)128U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  Hacl_Hash_SHA2_update_multi_512(s, blocks, blocks_n);
  Hacl_Hash_SHA2_update_last_512(s, (uint128_t)(uint64_t)blocks_len, rest, rest_len);
  Hacl_Hash_Core_SHA2_finish_512(s, dst);
}

static uint32_t
Hacl_Hash_Core_SHA2_h224[8U] =
  {
    (uint32_t)0xc1059ed8U, (uint32_t)0x367cd507U, (uint32_t)0x3070dd17U, (uint32_t)0xf70e5939U,
    (uint32_t)0xffc00b31U, (uint32_t)0x68581511U, (uint32_t)0x64f98fa7U, (uint32_t)0xbefa4fa4U
  };

static uint32_t
Hacl_Hash_Core_SHA2_h256[8U] =
  {
    (uint32_t)0x6a09e667U, (uint32_t)0xbb67ae85U, (uint32_t)0x3c6ef372U, (uint32_t)0xa54ff53aU,
    (uint32_t)0x510e527fU, (uint32_t)0x9b05688cU, (uint32_t)0x1f83d9abU, (uint32_t)0x5be0cd19U
  };

static uint64_t
Hacl_Hash_Core_SHA2_h384[8U] =
  {
    (uint64_t)0xcbbb9d5dc1059ed8U, (uint64_t)0x629a292a367cd507U, (uint64_t)0x9159015a3070dd17U,
    (uint64_t)0x152fecd8f70e5939U, (uint64_t)0x67332667ffc00b31U, (uint64_t)0x8eb44a8768581511U,
    (uint64_t)0xdb0c2e0d64f98fa7U, (uint64_t)0x47b5481dbefa4fa4U
  };

static uint64_t
Hacl_Hash_Core_SHA2_h512[8U] =
  {
    (uint64_t)0x6a09e667f3bcc908U, (uint64_t)0xbb67ae8584caa73bU, (uint64_t)0x3c6ef372fe94f82bU,
    (uint64_t)0xa54ff53a5f1d36f1U, (uint64_t)0x510e527fade682d1U, (uint64_t)0x9b05688c2b3e6c1fU,
    (uint64_t)0x1f83d9abfb41bd6bU, (uint64_t)0x5be0cd19137e2179U
  };

void Hacl_Hash_Core_SHA2_init_224(uint32_t *s)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    s[i] = Hacl_Hash_Core_SHA2_h224[i];
  }
}

void Hacl_Hash_Core_SHA2_init_256(uint32_t *s)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    s[i] = Hacl_Hash_Core_SHA2_h256[i];
  }
}

void Hacl_Hash_Core_SHA2_init_384(uint64_t *s)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    s[i] = Hacl_Hash_Core_SHA2_h384[i];
  }
}

void Hacl_Hash_Core_SHA2_init_512(uint64_t *s)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    s[i] = Hacl_Hash_Core_SHA2_h512[i];
  }
}

void Hacl_Hash_Core_SHA2_update_224(uint32_t *hash1, uint8_t *block)
{
  uint32_t hash11[8U] = { 0U };
  uint32_t computed_ws[64U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i = i + (uint32_t)1U)
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
  memcpy(hash11, hash1, (uint32_t)8U * sizeof hash1[0U]);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i = i + (uint32_t)1U)
  {
    uint32_t a0 = hash11[0U];
    uint32_t b0 = hash11[1U];
    uint32_t c0 = hash11[2U];
    uint32_t d0 = hash11[3U];
    uint32_t e0 = hash11[4U];
    uint32_t f0 = hash11[5U];
    uint32_t g0 = hash11[6U];
    uint32_t h03 = hash11[7U];
    uint32_t w = computed_ws[i];
    uint32_t
    t1 =
      h03
      +
        ((e0 >> (uint32_t)6U | e0 << (uint32_t)26U)
        ^ ((e0 >> (uint32_t)11U | e0 << (uint32_t)21U) ^ (e0 >> (uint32_t)25U | e0 << (uint32_t)7U)))
      + ((e0 & f0) ^ (~e0 & g0))
      + Hacl_Hash_Core_SHA2_Constants_k224_256[i]
      + w;
    uint32_t
    t2 =
      ((a0 >> (uint32_t)2U | a0 << (uint32_t)30U)
      ^ ((a0 >> (uint32_t)13U | a0 << (uint32_t)19U) ^ (a0 >> (uint32_t)22U | a0 << (uint32_t)10U)))
      + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
    hash11[0U] = t1 + t2;
    hash11[1U] = a0;
    hash11[2U] = b0;
    hash11[3U] = c0;
    hash11[4U] = d0 + t1;
    hash11[5U] = e0;
    hash11[6U] = f0;
    hash11[7U] = g0;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    uint32_t xi = hash1[i];
    uint32_t yi = hash11[i];
    hash1[i] = xi + yi;
  }
}

void Hacl_Hash_Core_SHA2_update_256(uint32_t *hash1, uint8_t *block)
{
  uint32_t hash11[8U] = { 0U };
  uint32_t computed_ws[64U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i = i + (uint32_t)1U)
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
  memcpy(hash11, hash1, (uint32_t)8U * sizeof hash1[0U]);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i = i + (uint32_t)1U)
  {
    uint32_t a0 = hash11[0U];
    uint32_t b0 = hash11[1U];
    uint32_t c0 = hash11[2U];
    uint32_t d0 = hash11[3U];
    uint32_t e0 = hash11[4U];
    uint32_t f0 = hash11[5U];
    uint32_t g0 = hash11[6U];
    uint32_t h03 = hash11[7U];
    uint32_t w = computed_ws[i];
    uint32_t
    t1 =
      h03
      +
        ((e0 >> (uint32_t)6U | e0 << (uint32_t)26U)
        ^ ((e0 >> (uint32_t)11U | e0 << (uint32_t)21U) ^ (e0 >> (uint32_t)25U | e0 << (uint32_t)7U)))
      + ((e0 & f0) ^ (~e0 & g0))
      + Hacl_Hash_Core_SHA2_Constants_k224_256[i]
      + w;
    uint32_t
    t2 =
      ((a0 >> (uint32_t)2U | a0 << (uint32_t)30U)
      ^ ((a0 >> (uint32_t)13U | a0 << (uint32_t)19U) ^ (a0 >> (uint32_t)22U | a0 << (uint32_t)10U)))
      + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
    hash11[0U] = t1 + t2;
    hash11[1U] = a0;
    hash11[2U] = b0;
    hash11[3U] = c0;
    hash11[4U] = d0 + t1;
    hash11[5U] = e0;
    hash11[6U] = f0;
    hash11[7U] = g0;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    uint32_t xi = hash1[i];
    uint32_t yi = hash11[i];
    hash1[i] = xi + yi;
  }
}

void Hacl_Hash_Core_SHA2_update_384(uint64_t *hash1, uint8_t *block)
{
  uint64_t hash11[8U] = { 0U };
  uint64_t computed_ws[80U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)80U; i = i + (uint32_t)1U)
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
  memcpy(hash11, hash1, (uint32_t)8U * sizeof hash1[0U]);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)80U; i = i + (uint32_t)1U)
  {
    uint64_t a0 = hash11[0U];
    uint64_t b0 = hash11[1U];
    uint64_t c0 = hash11[2U];
    uint64_t d0 = hash11[3U];
    uint64_t e0 = hash11[4U];
    uint64_t f0 = hash11[5U];
    uint64_t g0 = hash11[6U];
    uint64_t h03 = hash11[7U];
    uint64_t w = computed_ws[i];
    uint64_t
    t1 =
      h03
      +
        ((e0 >> (uint32_t)14U | e0 << (uint32_t)50U)
        ^
          ((e0 >> (uint32_t)18U | e0 << (uint32_t)46U)
          ^ (e0 >> (uint32_t)41U | e0 << (uint32_t)23U)))
      + ((e0 & f0) ^ (~e0 & g0))
      + Hacl_Hash_Core_SHA2_Constants_k384_512[i]
      + w;
    uint64_t
    t2 =
      ((a0 >> (uint32_t)28U | a0 << (uint32_t)36U)
      ^ ((a0 >> (uint32_t)34U | a0 << (uint32_t)30U) ^ (a0 >> (uint32_t)39U | a0 << (uint32_t)25U)))
      + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
    hash11[0U] = t1 + t2;
    hash11[1U] = a0;
    hash11[2U] = b0;
    hash11[3U] = c0;
    hash11[4U] = d0 + t1;
    hash11[5U] = e0;
    hash11[6U] = f0;
    hash11[7U] = g0;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    uint64_t xi = hash1[i];
    uint64_t yi = hash11[i];
    hash1[i] = xi + yi;
  }
}

void Hacl_Hash_Core_SHA2_update_512(uint64_t *hash1, uint8_t *block)
{
  uint64_t hash11[8U] = { 0U };
  uint64_t computed_ws[80U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)80U; i = i + (uint32_t)1U)
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
  memcpy(hash11, hash1, (uint32_t)8U * sizeof hash1[0U]);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)80U; i = i + (uint32_t)1U)
  {
    uint64_t a0 = hash11[0U];
    uint64_t b0 = hash11[1U];
    uint64_t c0 = hash11[2U];
    uint64_t d0 = hash11[3U];
    uint64_t e0 = hash11[4U];
    uint64_t f0 = hash11[5U];
    uint64_t g0 = hash11[6U];
    uint64_t h03 = hash11[7U];
    uint64_t w = computed_ws[i];
    uint64_t
    t1 =
      h03
      +
        ((e0 >> (uint32_t)14U | e0 << (uint32_t)50U)
        ^
          ((e0 >> (uint32_t)18U | e0 << (uint32_t)46U)
          ^ (e0 >> (uint32_t)41U | e0 << (uint32_t)23U)))
      + ((e0 & f0) ^ (~e0 & g0))
      + Hacl_Hash_Core_SHA2_Constants_k384_512[i]
      + w;
    uint64_t
    t2 =
      ((a0 >> (uint32_t)28U | a0 << (uint32_t)36U)
      ^ ((a0 >> (uint32_t)34U | a0 << (uint32_t)30U) ^ (a0 >> (uint32_t)39U | a0 << (uint32_t)25U)))
      + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
    hash11[0U] = t1 + t2;
    hash11[1U] = a0;
    hash11[2U] = b0;
    hash11[3U] = c0;
    hash11[4U] = d0 + t1;
    hash11[5U] = e0;
    hash11[6U] = f0;
    hash11[7U] = g0;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    uint64_t xi = hash1[i];
    uint64_t yi = hash11[i];
    hash1[i] = xi + yi;
  }
}

void Hacl_Hash_Core_SHA2_pad_224(uint64_t len, uint8_t *dst)
{
  uint8_t *dst1 = dst;
  dst1[0U] = (uint8_t)0x80U;
  uint8_t *dst2 = dst + (uint32_t)1U;
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    < ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(len % (uint64_t)(uint32_t)64U))) % (uint32_t)64U;
    i = i + (uint32_t)1U)
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

void Hacl_Hash_Core_SHA2_pad_256(uint64_t len, uint8_t *dst)
{
  uint8_t *dst1 = dst;
  dst1[0U] = (uint8_t)0x80U;
  uint8_t *dst2 = dst + (uint32_t)1U;
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    < ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(len % (uint64_t)(uint32_t)64U))) % (uint32_t)64U;
    i = i + (uint32_t)1U)
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

void Hacl_Hash_Core_SHA2_pad_384(uint128_t len, uint8_t *dst)
{
  uint8_t *dst1 = dst;
  dst1[0U] = (uint8_t)0x80U;
  uint8_t *dst2 = dst + (uint32_t)1U;
  uint32_t
  len_zero =
    ((uint32_t)256U - ((uint32_t)17U + (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)128U)))
    % (uint32_t)128U;
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    <
      ((uint32_t)256U - ((uint32_t)17U + (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)128U)))
      % (uint32_t)128U;
    i = i + (uint32_t)1U)
  {
    dst2[i] = (uint8_t)0U;
  }
  uint8_t
  *dst3 =
    dst
    +
      (uint32_t)1U
      +
        ((uint32_t)256U - ((uint32_t)17U + (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)128U)))
        % (uint32_t)128U;
  uint128_t len_ = len << (uint32_t)3U;
  store128_be(dst3, len_);
}

void Hacl_Hash_Core_SHA2_pad_512(uint128_t len, uint8_t *dst)
{
  uint8_t *dst1 = dst;
  dst1[0U] = (uint8_t)0x80U;
  uint8_t *dst2 = dst + (uint32_t)1U;
  uint32_t
  len_zero =
    ((uint32_t)256U - ((uint32_t)17U + (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)128U)))
    % (uint32_t)128U;
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    <
      ((uint32_t)256U - ((uint32_t)17U + (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)128U)))
      % (uint32_t)128U;
    i = i + (uint32_t)1U)
  {
    dst2[i] = (uint8_t)0U;
  }
  uint8_t
  *dst3 =
    dst
    +
      (uint32_t)1U
      +
        ((uint32_t)256U - ((uint32_t)17U + (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)128U)))
        % (uint32_t)128U;
  uint128_t len_ = len << (uint32_t)3U;
  store128_be(dst3, len_);
}

void Hacl_Hash_Core_SHA2_finish_224(uint32_t *s, uint8_t *dst)
{
  uint32_t *uu____0 = s;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)7U; i = i + (uint32_t)1U)
  {
    store32_be(dst + i * (uint32_t)4U, uu____0[i]);
  }
}

void Hacl_Hash_Core_SHA2_finish_256(uint32_t *s, uint8_t *dst)
{
  uint32_t *uu____0 = s;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    store32_be(dst + i * (uint32_t)4U, uu____0[i]);
  }
}

void Hacl_Hash_Core_SHA2_finish_384(uint64_t *s, uint8_t *dst)
{
  uint64_t *uu____0 = s;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)6U; i = i + (uint32_t)1U)
  {
    store64_be(dst + i * (uint32_t)8U, uu____0[i]);
  }
}

void Hacl_Hash_Core_SHA2_finish_512(uint64_t *s, uint8_t *dst)
{
  uint64_t *uu____0 = s;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    store64_be(dst + i * (uint32_t)8U, uu____0[i]);
  }
}

uint32_t
Hacl_Hash_Core_SHA2_Constants_k224_256[64U] =
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

uint64_t
Hacl_Hash_Core_SHA2_Constants_k384_512[80U] =
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

