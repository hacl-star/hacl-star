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


#include "Hacl_Hash_MD5.h"

static u32
_t[64U] =
  {
    (u32)0xd76aa478U, (u32)0xe8c7b756U, (u32)0x242070dbU, (u32)0xc1bdceeeU, (u32)0xf57c0fafU,
    (u32)0x4787c62aU, (u32)0xa8304613U, (u32)0xfd469501U, (u32)0x698098d8U, (u32)0x8b44f7afU,
    (u32)0xffff5bb1U, (u32)0x895cd7beU, (u32)0x6b901122U, (u32)0xfd987193U, (u32)0xa679438eU,
    (u32)0x49b40821U, (u32)0xf61e2562U, (u32)0xc040b340U, (u32)0x265e5a51U, (u32)0xe9b6c7aaU,
    (u32)0xd62f105dU, (u32)0x02441453U, (u32)0xd8a1e681U, (u32)0xe7d3fbc8U, (u32)0x21e1cde6U,
    (u32)0xc33707d6U, (u32)0xf4d50d87U, (u32)0x455a14edU, (u32)0xa9e3e905U, (u32)0xfcefa3f8U,
    (u32)0x676f02d9U, (u32)0x8d2a4c8aU, (u32)0xfffa3942U, (u32)0x8771f681U, (u32)0x6d9d6122U,
    (u32)0xfde5380cU, (u32)0xa4beea44U, (u32)0x4bdecfa9U, (u32)0xf6bb4b60U, (u32)0xbebfbc70U,
    (u32)0x289b7ec6U, (u32)0xeaa127faU, (u32)0xd4ef3085U, (u32)0x4881d05U, (u32)0xd9d4d039U,
    (u32)0xe6db99e5U, (u32)0x1fa27cf8U, (u32)0xc4ac5665U, (u32)0xf4292244U, (u32)0x432aff97U,
    (u32)0xab9423a7U, (u32)0xfc93a039U, (u32)0x655b59c3U, (u32)0x8f0ccc92U, (u32)0xffeff47dU,
    (u32)0x85845dd1U, (u32)0x6fa87e4fU, (u32)0xfe2ce6e0U, (u32)0xa3014314U, (u32)0x4e0811a1U,
    (u32)0xf7537e82U, (u32)0xbd3af235U, (u32)0x2ad7d2bbU, (u32)0xeb86d391U
  };

static void legacy_update(u32 *abcd, u8 *x)
{
  u32 aa = abcd[0U];
  u32 bb = abcd[1U];
  u32 cc = abcd[2U];
  u32 dd = abcd[3U];
  u32 va0 = abcd[0U];
  u32 vb0 = abcd[1U];
  u32 vc0 = abcd[2U];
  u32 vd0 = abcd[3U];
  u8 *b0 = x;
  u32 u0 = load32_le(b0);
  u32 xk0 = u0;
  u32 ti0 = _t[0U];
  u32
  v0 =
    vb0
    +
      ((va0 + ((vb0 & vc0) | (~vb0 & vd0)) + xk0 + ti0)
      << (u32)7U
      | (va0 + ((vb0 & vc0) | (~vb0 & vd0)) + xk0 + ti0) >> (u32)25U);
  u32 va1;
  u32 vb1;
  u32 vc1;
  u32 vd1;
  u8 *b1;
  u32 u1;
  u32 xk1;
  u32 ti1;
  u32 v1;
  u32 va2;
  u32 vb2;
  u32 vc2;
  u32 vd2;
  u8 *b2;
  u32 u2;
  u32 xk2;
  u32 ti2;
  u32 v2;
  u32 va3;
  u32 vb3;
  u32 vc3;
  u32 vd3;
  u8 *b3;
  u32 u3;
  u32 xk3;
  u32 ti3;
  u32 v3;
  u32 va4;
  u32 vb4;
  u32 vc4;
  u32 vd4;
  u8 *b4;
  u32 u4;
  u32 xk4;
  u32 ti4;
  u32 v4;
  u32 va5;
  u32 vb5;
  u32 vc5;
  u32 vd5;
  u8 *b5;
  u32 u5;
  u32 xk5;
  u32 ti5;
  u32 v5;
  u32 va6;
  u32 vb6;
  u32 vc6;
  u32 vd6;
  u8 *b6;
  u32 u6;
  u32 xk6;
  u32 ti6;
  u32 v6;
  u32 va7;
  u32 vb7;
  u32 vc7;
  u32 vd7;
  u8 *b7;
  u32 u7;
  u32 xk7;
  u32 ti7;
  u32 v7;
  u32 va8;
  u32 vb8;
  u32 vc8;
  u32 vd8;
  u8 *b8;
  u32 u8;
  u32 xk8;
  u32 ti8;
  u32 v8;
  u32 va9;
  u32 vb9;
  u32 vc9;
  u32 vd9;
  u8 *b9;
  u32 u9;
  u32 xk9;
  u32 ti9;
  u32 v9;
  u32 va10;
  u32 vb10;
  u32 vc10;
  u32 vd10;
  u8 *b10;
  u32 u10;
  u32 xk10;
  u32 ti10;
  u32 v10;
  u32 va11;
  u32 vb11;
  u32 vc11;
  u32 vd11;
  u8 *b11;
  u32 u11;
  u32 xk11;
  u32 ti11;
  u32 v11;
  u32 va12;
  u32 vb12;
  u32 vc12;
  u32 vd12;
  u8 *b12;
  u32 u12;
  u32 xk12;
  u32 ti12;
  u32 v12;
  u32 va13;
  u32 vb13;
  u32 vc13;
  u32 vd13;
  u8 *b13;
  u32 u13;
  u32 xk13;
  u32 ti13;
  u32 v13;
  u32 va14;
  u32 vb14;
  u32 vc14;
  u32 vd14;
  u8 *b14;
  u32 u14;
  u32 xk14;
  u32 ti14;
  u32 v14;
  u32 va15;
  u32 vb15;
  u32 vc15;
  u32 vd15;
  u8 *b15;
  u32 u15;
  u32 xk15;
  u32 ti15;
  u32 v15;
  u32 va16;
  u32 vb16;
  u32 vc16;
  u32 vd16;
  u8 *b16;
  u32 u16;
  u32 xk16;
  u32 ti16;
  u32 v16;
  u32 va17;
  u32 vb17;
  u32 vc17;
  u32 vd17;
  u8 *b17;
  u32 u17;
  u32 xk17;
  u32 ti17;
  u32 v17;
  u32 va18;
  u32 vb18;
  u32 vc18;
  u32 vd18;
  u8 *b18;
  u32 u18;
  u32 xk18;
  u32 ti18;
  u32 v18;
  u32 va19;
  u32 vb19;
  u32 vc19;
  u32 vd19;
  u8 *b19;
  u32 u19;
  u32 xk19;
  u32 ti19;
  u32 v19;
  u32 va20;
  u32 vb20;
  u32 vc20;
  u32 vd20;
  u8 *b20;
  u32 u20;
  u32 xk20;
  u32 ti20;
  u32 v20;
  u32 va21;
  u32 vb21;
  u32 vc21;
  u32 vd21;
  u8 *b21;
  u32 u21;
  u32 xk21;
  u32 ti21;
  u32 v21;
  u32 va22;
  u32 vb22;
  u32 vc22;
  u32 vd22;
  u8 *b22;
  u32 u22;
  u32 xk22;
  u32 ti22;
  u32 v22;
  u32 va23;
  u32 vb23;
  u32 vc23;
  u32 vd23;
  u8 *b23;
  u32 u23;
  u32 xk23;
  u32 ti23;
  u32 v23;
  u32 va24;
  u32 vb24;
  u32 vc24;
  u32 vd24;
  u8 *b24;
  u32 u24;
  u32 xk24;
  u32 ti24;
  u32 v24;
  u32 va25;
  u32 vb25;
  u32 vc25;
  u32 vd25;
  u8 *b25;
  u32 u25;
  u32 xk25;
  u32 ti25;
  u32 v25;
  u32 va26;
  u32 vb26;
  u32 vc26;
  u32 vd26;
  u8 *b26;
  u32 u26;
  u32 xk26;
  u32 ti26;
  u32 v26;
  u32 va27;
  u32 vb27;
  u32 vc27;
  u32 vd27;
  u8 *b27;
  u32 u27;
  u32 xk27;
  u32 ti27;
  u32 v27;
  u32 va28;
  u32 vb28;
  u32 vc28;
  u32 vd28;
  u8 *b28;
  u32 u28;
  u32 xk28;
  u32 ti28;
  u32 v28;
  u32 va29;
  u32 vb29;
  u32 vc29;
  u32 vd29;
  u8 *b29;
  u32 u29;
  u32 xk29;
  u32 ti29;
  u32 v29;
  u32 va30;
  u32 vb30;
  u32 vc30;
  u32 vd30;
  u8 *b30;
  u32 u30;
  u32 xk30;
  u32 ti30;
  u32 v30;
  u32 va31;
  u32 vb31;
  u32 vc31;
  u32 vd31;
  u8 *b31;
  u32 u31;
  u32 xk31;
  u32 ti31;
  u32 v31;
  u32 va32;
  u32 vb32;
  u32 vc32;
  u32 vd32;
  u8 *b32;
  u32 u32;
  u32 xk32;
  u32 ti32;
  u32 v32;
  u32 va33;
  u32 vb33;
  u32 vc33;
  u32 vd33;
  u8 *b33;
  u32 u33;
  u32 xk33;
  u32 ti33;
  u32 v33;
  u32 va34;
  u32 vb34;
  u32 vc34;
  u32 vd34;
  u8 *b34;
  u32 u34;
  u32 xk34;
  u32 ti34;
  u32 v34;
  u32 va35;
  u32 vb35;
  u32 vc35;
  u32 vd35;
  u8 *b35;
  u32 u35;
  u32 xk35;
  u32 ti35;
  u32 v35;
  u32 va36;
  u32 vb36;
  u32 vc36;
  u32 vd36;
  u8 *b36;
  u32 u36;
  u32 xk36;
  u32 ti36;
  u32 v36;
  u32 va37;
  u32 vb37;
  u32 vc37;
  u32 vd37;
  u8 *b37;
  u32 u37;
  u32 xk37;
  u32 ti37;
  u32 v37;
  u32 va38;
  u32 vb38;
  u32 vc38;
  u32 vd38;
  u8 *b38;
  u32 u38;
  u32 xk38;
  u32 ti38;
  u32 v38;
  u32 va39;
  u32 vb39;
  u32 vc39;
  u32 vd39;
  u8 *b39;
  u32 u39;
  u32 xk39;
  u32 ti39;
  u32 v39;
  u32 va40;
  u32 vb40;
  u32 vc40;
  u32 vd40;
  u8 *b40;
  u32 u40;
  u32 xk40;
  u32 ti40;
  u32 v40;
  u32 va41;
  u32 vb41;
  u32 vc41;
  u32 vd41;
  u8 *b41;
  u32 u41;
  u32 xk41;
  u32 ti41;
  u32 v41;
  u32 va42;
  u32 vb42;
  u32 vc42;
  u32 vd42;
  u8 *b42;
  u32 u42;
  u32 xk42;
  u32 ti42;
  u32 v42;
  u32 va43;
  u32 vb43;
  u32 vc43;
  u32 vd43;
  u8 *b43;
  u32 u43;
  u32 xk43;
  u32 ti43;
  u32 v43;
  u32 va44;
  u32 vb44;
  u32 vc44;
  u32 vd44;
  u8 *b44;
  u32 u44;
  u32 xk44;
  u32 ti44;
  u32 v44;
  u32 va45;
  u32 vb45;
  u32 vc45;
  u32 vd45;
  u8 *b45;
  u32 u45;
  u32 xk45;
  u32 ti45;
  u32 v45;
  u32 va46;
  u32 vb46;
  u32 vc46;
  u32 vd46;
  u8 *b46;
  u32 u46;
  u32 xk46;
  u32 ti46;
  u32 v46;
  u32 va47;
  u32 vb47;
  u32 vc47;
  u32 vd47;
  u8 *b47;
  u32 u47;
  u32 xk47;
  u32 ti47;
  u32 v47;
  u32 va48;
  u32 vb48;
  u32 vc48;
  u32 vd48;
  u8 *b48;
  u32 u48;
  u32 xk48;
  u32 ti48;
  u32 v48;
  u32 va49;
  u32 vb49;
  u32 vc49;
  u32 vd49;
  u8 *b49;
  u32 u49;
  u32 xk49;
  u32 ti49;
  u32 v49;
  u32 va50;
  u32 vb50;
  u32 vc50;
  u32 vd50;
  u8 *b50;
  u32 u50;
  u32 xk50;
  u32 ti50;
  u32 v50;
  u32 va51;
  u32 vb51;
  u32 vc51;
  u32 vd51;
  u8 *b51;
  u32 u51;
  u32 xk51;
  u32 ti51;
  u32 v51;
  u32 va52;
  u32 vb52;
  u32 vc52;
  u32 vd52;
  u8 *b52;
  u32 u52;
  u32 xk52;
  u32 ti52;
  u32 v52;
  u32 va53;
  u32 vb53;
  u32 vc53;
  u32 vd53;
  u8 *b53;
  u32 u53;
  u32 xk53;
  u32 ti53;
  u32 v53;
  u32 va54;
  u32 vb54;
  u32 vc54;
  u32 vd54;
  u8 *b54;
  u32 u54;
  u32 xk54;
  u32 ti54;
  u32 v54;
  u32 va55;
  u32 vb55;
  u32 vc55;
  u32 vd55;
  u8 *b55;
  u32 u55;
  u32 xk55;
  u32 ti55;
  u32 v55;
  u32 va56;
  u32 vb56;
  u32 vc56;
  u32 vd56;
  u8 *b56;
  u32 u56;
  u32 xk56;
  u32 ti56;
  u32 v56;
  u32 va57;
  u32 vb57;
  u32 vc57;
  u32 vd57;
  u8 *b57;
  u32 u57;
  u32 xk57;
  u32 ti57;
  u32 v57;
  u32 va58;
  u32 vb58;
  u32 vc58;
  u32 vd58;
  u8 *b58;
  u32 u58;
  u32 xk58;
  u32 ti58;
  u32 v58;
  u32 va59;
  u32 vb59;
  u32 vc59;
  u32 vd59;
  u8 *b59;
  u32 u59;
  u32 xk59;
  u32 ti59;
  u32 v59;
  u32 va60;
  u32 vb60;
  u32 vc60;
  u32 vd60;
  u8 *b60;
  u32 u60;
  u32 xk60;
  u32 ti60;
  u32 v60;
  u32 va61;
  u32 vb61;
  u32 vc61;
  u32 vd61;
  u8 *b61;
  u32 u61;
  u32 xk61;
  u32 ti61;
  u32 v61;
  u32 va62;
  u32 vb62;
  u32 vc62;
  u32 vd62;
  u8 *b62;
  u32 u62;
  u32 xk62;
  u32 ti62;
  u32 v62;
  u32 va;
  u32 vb;
  u32 vc;
  u32 vd;
  u8 *b63;
  u32 u;
  u32 xk;
  u32 ti;
  u32 v;
  u32 a;
  u32 b;
  u32 c;
  u32 d;
  abcd[0U] = v0;
  va1 = abcd[3U];
  vb1 = abcd[0U];
  vc1 = abcd[1U];
  vd1 = abcd[2U];
  b1 = x + (u32)4U;
  u1 = load32_le(b1);
  xk1 = u1;
  ti1 = _t[1U];
  v1 =
    vb1
    +
      ((va1 + ((vb1 & vc1) | (~vb1 & vd1)) + xk1 + ti1)
      << (u32)12U
      | (va1 + ((vb1 & vc1) | (~vb1 & vd1)) + xk1 + ti1) >> (u32)20U);
  abcd[3U] = v1;
  va2 = abcd[2U];
  vb2 = abcd[3U];
  vc2 = abcd[0U];
  vd2 = abcd[1U];
  b2 = x + (u32)8U;
  u2 = load32_le(b2);
  xk2 = u2;
  ti2 = _t[2U];
  v2 =
    vb2
    +
      ((va2 + ((vb2 & vc2) | (~vb2 & vd2)) + xk2 + ti2)
      << (u32)17U
      | (va2 + ((vb2 & vc2) | (~vb2 & vd2)) + xk2 + ti2) >> (u32)15U);
  abcd[2U] = v2;
  va3 = abcd[1U];
  vb3 = abcd[2U];
  vc3 = abcd[3U];
  vd3 = abcd[0U];
  b3 = x + (u32)12U;
  u3 = load32_le(b3);
  xk3 = u3;
  ti3 = _t[3U];
  v3 =
    vb3
    +
      ((va3 + ((vb3 & vc3) | (~vb3 & vd3)) + xk3 + ti3)
      << (u32)22U
      | (va3 + ((vb3 & vc3) | (~vb3 & vd3)) + xk3 + ti3) >> (u32)10U);
  abcd[1U] = v3;
  va4 = abcd[0U];
  vb4 = abcd[1U];
  vc4 = abcd[2U];
  vd4 = abcd[3U];
  b4 = x + (u32)16U;
  u4 = load32_le(b4);
  xk4 = u4;
  ti4 = _t[4U];
  v4 =
    vb4
    +
      ((va4 + ((vb4 & vc4) | (~vb4 & vd4)) + xk4 + ti4)
      << (u32)7U
      | (va4 + ((vb4 & vc4) | (~vb4 & vd4)) + xk4 + ti4) >> (u32)25U);
  abcd[0U] = v4;
  va5 = abcd[3U];
  vb5 = abcd[0U];
  vc5 = abcd[1U];
  vd5 = abcd[2U];
  b5 = x + (u32)20U;
  u5 = load32_le(b5);
  xk5 = u5;
  ti5 = _t[5U];
  v5 =
    vb5
    +
      ((va5 + ((vb5 & vc5) | (~vb5 & vd5)) + xk5 + ti5)
      << (u32)12U
      | (va5 + ((vb5 & vc5) | (~vb5 & vd5)) + xk5 + ti5) >> (u32)20U);
  abcd[3U] = v5;
  va6 = abcd[2U];
  vb6 = abcd[3U];
  vc6 = abcd[0U];
  vd6 = abcd[1U];
  b6 = x + (u32)24U;
  u6 = load32_le(b6);
  xk6 = u6;
  ti6 = _t[6U];
  v6 =
    vb6
    +
      ((va6 + ((vb6 & vc6) | (~vb6 & vd6)) + xk6 + ti6)
      << (u32)17U
      | (va6 + ((vb6 & vc6) | (~vb6 & vd6)) + xk6 + ti6) >> (u32)15U);
  abcd[2U] = v6;
  va7 = abcd[1U];
  vb7 = abcd[2U];
  vc7 = abcd[3U];
  vd7 = abcd[0U];
  b7 = x + (u32)28U;
  u7 = load32_le(b7);
  xk7 = u7;
  ti7 = _t[7U];
  v7 =
    vb7
    +
      ((va7 + ((vb7 & vc7) | (~vb7 & vd7)) + xk7 + ti7)
      << (u32)22U
      | (va7 + ((vb7 & vc7) | (~vb7 & vd7)) + xk7 + ti7) >> (u32)10U);
  abcd[1U] = v7;
  va8 = abcd[0U];
  vb8 = abcd[1U];
  vc8 = abcd[2U];
  vd8 = abcd[3U];
  b8 = x + (u32)32U;
  u8 = load32_le(b8);
  xk8 = u8;
  ti8 = _t[8U];
  v8 =
    vb8
    +
      ((va8 + ((vb8 & vc8) | (~vb8 & vd8)) + xk8 + ti8)
      << (u32)7U
      | (va8 + ((vb8 & vc8) | (~vb8 & vd8)) + xk8 + ti8) >> (u32)25U);
  abcd[0U] = v8;
  va9 = abcd[3U];
  vb9 = abcd[0U];
  vc9 = abcd[1U];
  vd9 = abcd[2U];
  b9 = x + (u32)36U;
  u9 = load32_le(b9);
  xk9 = u9;
  ti9 = _t[9U];
  v9 =
    vb9
    +
      ((va9 + ((vb9 & vc9) | (~vb9 & vd9)) + xk9 + ti9)
      << (u32)12U
      | (va9 + ((vb9 & vc9) | (~vb9 & vd9)) + xk9 + ti9) >> (u32)20U);
  abcd[3U] = v9;
  va10 = abcd[2U];
  vb10 = abcd[3U];
  vc10 = abcd[0U];
  vd10 = abcd[1U];
  b10 = x + (u32)40U;
  u10 = load32_le(b10);
  xk10 = u10;
  ti10 = _t[10U];
  v10 =
    vb10
    +
      ((va10 + ((vb10 & vc10) | (~vb10 & vd10)) + xk10 + ti10)
      << (u32)17U
      | (va10 + ((vb10 & vc10) | (~vb10 & vd10)) + xk10 + ti10) >> (u32)15U);
  abcd[2U] = v10;
  va11 = abcd[1U];
  vb11 = abcd[2U];
  vc11 = abcd[3U];
  vd11 = abcd[0U];
  b11 = x + (u32)44U;
  u11 = load32_le(b11);
  xk11 = u11;
  ti11 = _t[11U];
  v11 =
    vb11
    +
      ((va11 + ((vb11 & vc11) | (~vb11 & vd11)) + xk11 + ti11)
      << (u32)22U
      | (va11 + ((vb11 & vc11) | (~vb11 & vd11)) + xk11 + ti11) >> (u32)10U);
  abcd[1U] = v11;
  va12 = abcd[0U];
  vb12 = abcd[1U];
  vc12 = abcd[2U];
  vd12 = abcd[3U];
  b12 = x + (u32)48U;
  u12 = load32_le(b12);
  xk12 = u12;
  ti12 = _t[12U];
  v12 =
    vb12
    +
      ((va12 + ((vb12 & vc12) | (~vb12 & vd12)) + xk12 + ti12)
      << (u32)7U
      | (va12 + ((vb12 & vc12) | (~vb12 & vd12)) + xk12 + ti12) >> (u32)25U);
  abcd[0U] = v12;
  va13 = abcd[3U];
  vb13 = abcd[0U];
  vc13 = abcd[1U];
  vd13 = abcd[2U];
  b13 = x + (u32)52U;
  u13 = load32_le(b13);
  xk13 = u13;
  ti13 = _t[13U];
  v13 =
    vb13
    +
      ((va13 + ((vb13 & vc13) | (~vb13 & vd13)) + xk13 + ti13)
      << (u32)12U
      | (va13 + ((vb13 & vc13) | (~vb13 & vd13)) + xk13 + ti13) >> (u32)20U);
  abcd[3U] = v13;
  va14 = abcd[2U];
  vb14 = abcd[3U];
  vc14 = abcd[0U];
  vd14 = abcd[1U];
  b14 = x + (u32)56U;
  u14 = load32_le(b14);
  xk14 = u14;
  ti14 = _t[14U];
  v14 =
    vb14
    +
      ((va14 + ((vb14 & vc14) | (~vb14 & vd14)) + xk14 + ti14)
      << (u32)17U
      | (va14 + ((vb14 & vc14) | (~vb14 & vd14)) + xk14 + ti14) >> (u32)15U);
  abcd[2U] = v14;
  va15 = abcd[1U];
  vb15 = abcd[2U];
  vc15 = abcd[3U];
  vd15 = abcd[0U];
  b15 = x + (u32)60U;
  u15 = load32_le(b15);
  xk15 = u15;
  ti15 = _t[15U];
  v15 =
    vb15
    +
      ((va15 + ((vb15 & vc15) | (~vb15 & vd15)) + xk15 + ti15)
      << (u32)22U
      | (va15 + ((vb15 & vc15) | (~vb15 & vd15)) + xk15 + ti15) >> (u32)10U);
  abcd[1U] = v15;
  va16 = abcd[0U];
  vb16 = abcd[1U];
  vc16 = abcd[2U];
  vd16 = abcd[3U];
  b16 = x + (u32)4U;
  u16 = load32_le(b16);
  xk16 = u16;
  ti16 = _t[16U];
  v16 =
    vb16
    +
      ((va16 + ((vb16 & vd16) | (vc16 & ~vd16)) + xk16 + ti16)
      << (u32)5U
      | (va16 + ((vb16 & vd16) | (vc16 & ~vd16)) + xk16 + ti16) >> (u32)27U);
  abcd[0U] = v16;
  va17 = abcd[3U];
  vb17 = abcd[0U];
  vc17 = abcd[1U];
  vd17 = abcd[2U];
  b17 = x + (u32)24U;
  u17 = load32_le(b17);
  xk17 = u17;
  ti17 = _t[17U];
  v17 =
    vb17
    +
      ((va17 + ((vb17 & vd17) | (vc17 & ~vd17)) + xk17 + ti17)
      << (u32)9U
      | (va17 + ((vb17 & vd17) | (vc17 & ~vd17)) + xk17 + ti17) >> (u32)23U);
  abcd[3U] = v17;
  va18 = abcd[2U];
  vb18 = abcd[3U];
  vc18 = abcd[0U];
  vd18 = abcd[1U];
  b18 = x + (u32)44U;
  u18 = load32_le(b18);
  xk18 = u18;
  ti18 = _t[18U];
  v18 =
    vb18
    +
      ((va18 + ((vb18 & vd18) | (vc18 & ~vd18)) + xk18 + ti18)
      << (u32)14U
      | (va18 + ((vb18 & vd18) | (vc18 & ~vd18)) + xk18 + ti18) >> (u32)18U);
  abcd[2U] = v18;
  va19 = abcd[1U];
  vb19 = abcd[2U];
  vc19 = abcd[3U];
  vd19 = abcd[0U];
  b19 = x;
  u19 = load32_le(b19);
  xk19 = u19;
  ti19 = _t[19U];
  v19 =
    vb19
    +
      ((va19 + ((vb19 & vd19) | (vc19 & ~vd19)) + xk19 + ti19)
      << (u32)20U
      | (va19 + ((vb19 & vd19) | (vc19 & ~vd19)) + xk19 + ti19) >> (u32)12U);
  abcd[1U] = v19;
  va20 = abcd[0U];
  vb20 = abcd[1U];
  vc20 = abcd[2U];
  vd20 = abcd[3U];
  b20 = x + (u32)20U;
  u20 = load32_le(b20);
  xk20 = u20;
  ti20 = _t[20U];
  v20 =
    vb20
    +
      ((va20 + ((vb20 & vd20) | (vc20 & ~vd20)) + xk20 + ti20)
      << (u32)5U
      | (va20 + ((vb20 & vd20) | (vc20 & ~vd20)) + xk20 + ti20) >> (u32)27U);
  abcd[0U] = v20;
  va21 = abcd[3U];
  vb21 = abcd[0U];
  vc21 = abcd[1U];
  vd21 = abcd[2U];
  b21 = x + (u32)40U;
  u21 = load32_le(b21);
  xk21 = u21;
  ti21 = _t[21U];
  v21 =
    vb21
    +
      ((va21 + ((vb21 & vd21) | (vc21 & ~vd21)) + xk21 + ti21)
      << (u32)9U
      | (va21 + ((vb21 & vd21) | (vc21 & ~vd21)) + xk21 + ti21) >> (u32)23U);
  abcd[3U] = v21;
  va22 = abcd[2U];
  vb22 = abcd[3U];
  vc22 = abcd[0U];
  vd22 = abcd[1U];
  b22 = x + (u32)60U;
  u22 = load32_le(b22);
  xk22 = u22;
  ti22 = _t[22U];
  v22 =
    vb22
    +
      ((va22 + ((vb22 & vd22) | (vc22 & ~vd22)) + xk22 + ti22)
      << (u32)14U
      | (va22 + ((vb22 & vd22) | (vc22 & ~vd22)) + xk22 + ti22) >> (u32)18U);
  abcd[2U] = v22;
  va23 = abcd[1U];
  vb23 = abcd[2U];
  vc23 = abcd[3U];
  vd23 = abcd[0U];
  b23 = x + (u32)16U;
  u23 = load32_le(b23);
  xk23 = u23;
  ti23 = _t[23U];
  v23 =
    vb23
    +
      ((va23 + ((vb23 & vd23) | (vc23 & ~vd23)) + xk23 + ti23)
      << (u32)20U
      | (va23 + ((vb23 & vd23) | (vc23 & ~vd23)) + xk23 + ti23) >> (u32)12U);
  abcd[1U] = v23;
  va24 = abcd[0U];
  vb24 = abcd[1U];
  vc24 = abcd[2U];
  vd24 = abcd[3U];
  b24 = x + (u32)36U;
  u24 = load32_le(b24);
  xk24 = u24;
  ti24 = _t[24U];
  v24 =
    vb24
    +
      ((va24 + ((vb24 & vd24) | (vc24 & ~vd24)) + xk24 + ti24)
      << (u32)5U
      | (va24 + ((vb24 & vd24) | (vc24 & ~vd24)) + xk24 + ti24) >> (u32)27U);
  abcd[0U] = v24;
  va25 = abcd[3U];
  vb25 = abcd[0U];
  vc25 = abcd[1U];
  vd25 = abcd[2U];
  b25 = x + (u32)56U;
  u25 = load32_le(b25);
  xk25 = u25;
  ti25 = _t[25U];
  v25 =
    vb25
    +
      ((va25 + ((vb25 & vd25) | (vc25 & ~vd25)) + xk25 + ti25)
      << (u32)9U
      | (va25 + ((vb25 & vd25) | (vc25 & ~vd25)) + xk25 + ti25) >> (u32)23U);
  abcd[3U] = v25;
  va26 = abcd[2U];
  vb26 = abcd[3U];
  vc26 = abcd[0U];
  vd26 = abcd[1U];
  b26 = x + (u32)12U;
  u26 = load32_le(b26);
  xk26 = u26;
  ti26 = _t[26U];
  v26 =
    vb26
    +
      ((va26 + ((vb26 & vd26) | (vc26 & ~vd26)) + xk26 + ti26)
      << (u32)14U
      | (va26 + ((vb26 & vd26) | (vc26 & ~vd26)) + xk26 + ti26) >> (u32)18U);
  abcd[2U] = v26;
  va27 = abcd[1U];
  vb27 = abcd[2U];
  vc27 = abcd[3U];
  vd27 = abcd[0U];
  b27 = x + (u32)32U;
  u27 = load32_le(b27);
  xk27 = u27;
  ti27 = _t[27U];
  v27 =
    vb27
    +
      ((va27 + ((vb27 & vd27) | (vc27 & ~vd27)) + xk27 + ti27)
      << (u32)20U
      | (va27 + ((vb27 & vd27) | (vc27 & ~vd27)) + xk27 + ti27) >> (u32)12U);
  abcd[1U] = v27;
  va28 = abcd[0U];
  vb28 = abcd[1U];
  vc28 = abcd[2U];
  vd28 = abcd[3U];
  b28 = x + (u32)52U;
  u28 = load32_le(b28);
  xk28 = u28;
  ti28 = _t[28U];
  v28 =
    vb28
    +
      ((va28 + ((vb28 & vd28) | (vc28 & ~vd28)) + xk28 + ti28)
      << (u32)5U
      | (va28 + ((vb28 & vd28) | (vc28 & ~vd28)) + xk28 + ti28) >> (u32)27U);
  abcd[0U] = v28;
  va29 = abcd[3U];
  vb29 = abcd[0U];
  vc29 = abcd[1U];
  vd29 = abcd[2U];
  b29 = x + (u32)8U;
  u29 = load32_le(b29);
  xk29 = u29;
  ti29 = _t[29U];
  v29 =
    vb29
    +
      ((va29 + ((vb29 & vd29) | (vc29 & ~vd29)) + xk29 + ti29)
      << (u32)9U
      | (va29 + ((vb29 & vd29) | (vc29 & ~vd29)) + xk29 + ti29) >> (u32)23U);
  abcd[3U] = v29;
  va30 = abcd[2U];
  vb30 = abcd[3U];
  vc30 = abcd[0U];
  vd30 = abcd[1U];
  b30 = x + (u32)28U;
  u30 = load32_le(b30);
  xk30 = u30;
  ti30 = _t[30U];
  v30 =
    vb30
    +
      ((va30 + ((vb30 & vd30) | (vc30 & ~vd30)) + xk30 + ti30)
      << (u32)14U
      | (va30 + ((vb30 & vd30) | (vc30 & ~vd30)) + xk30 + ti30) >> (u32)18U);
  abcd[2U] = v30;
  va31 = abcd[1U];
  vb31 = abcd[2U];
  vc31 = abcd[3U];
  vd31 = abcd[0U];
  b31 = x + (u32)48U;
  u31 = load32_le(b31);
  xk31 = u31;
  ti31 = _t[31U];
  v31 =
    vb31
    +
      ((va31 + ((vb31 & vd31) | (vc31 & ~vd31)) + xk31 + ti31)
      << (u32)20U
      | (va31 + ((vb31 & vd31) | (vc31 & ~vd31)) + xk31 + ti31) >> (u32)12U);
  abcd[1U] = v31;
  va32 = abcd[0U];
  vb32 = abcd[1U];
  vc32 = abcd[2U];
  vd32 = abcd[3U];
  b32 = x + (u32)20U;
  u32 = load32_le(b32);
  xk32 = u32;
  ti32 = _t[32U];
  v32 =
    vb32
    +
      ((va32 + (vb32 ^ (vc32 ^ vd32)) + xk32 + ti32)
      << (u32)4U
      | (va32 + (vb32 ^ (vc32 ^ vd32)) + xk32 + ti32) >> (u32)28U);
  abcd[0U] = v32;
  va33 = abcd[3U];
  vb33 = abcd[0U];
  vc33 = abcd[1U];
  vd33 = abcd[2U];
  b33 = x + (u32)32U;
  u33 = load32_le(b33);
  xk33 = u33;
  ti33 = _t[33U];
  v33 =
    vb33
    +
      ((va33 + (vb33 ^ (vc33 ^ vd33)) + xk33 + ti33)
      << (u32)11U
      | (va33 + (vb33 ^ (vc33 ^ vd33)) + xk33 + ti33) >> (u32)21U);
  abcd[3U] = v33;
  va34 = abcd[2U];
  vb34 = abcd[3U];
  vc34 = abcd[0U];
  vd34 = abcd[1U];
  b34 = x + (u32)44U;
  u34 = load32_le(b34);
  xk34 = u34;
  ti34 = _t[34U];
  v34 =
    vb34
    +
      ((va34 + (vb34 ^ (vc34 ^ vd34)) + xk34 + ti34)
      << (u32)16U
      | (va34 + (vb34 ^ (vc34 ^ vd34)) + xk34 + ti34) >> (u32)16U);
  abcd[2U] = v34;
  va35 = abcd[1U];
  vb35 = abcd[2U];
  vc35 = abcd[3U];
  vd35 = abcd[0U];
  b35 = x + (u32)56U;
  u35 = load32_le(b35);
  xk35 = u35;
  ti35 = _t[35U];
  v35 =
    vb35
    +
      ((va35 + (vb35 ^ (vc35 ^ vd35)) + xk35 + ti35)
      << (u32)23U
      | (va35 + (vb35 ^ (vc35 ^ vd35)) + xk35 + ti35) >> (u32)9U);
  abcd[1U] = v35;
  va36 = abcd[0U];
  vb36 = abcd[1U];
  vc36 = abcd[2U];
  vd36 = abcd[3U];
  b36 = x + (u32)4U;
  u36 = load32_le(b36);
  xk36 = u36;
  ti36 = _t[36U];
  v36 =
    vb36
    +
      ((va36 + (vb36 ^ (vc36 ^ vd36)) + xk36 + ti36)
      << (u32)4U
      | (va36 + (vb36 ^ (vc36 ^ vd36)) + xk36 + ti36) >> (u32)28U);
  abcd[0U] = v36;
  va37 = abcd[3U];
  vb37 = abcd[0U];
  vc37 = abcd[1U];
  vd37 = abcd[2U];
  b37 = x + (u32)16U;
  u37 = load32_le(b37);
  xk37 = u37;
  ti37 = _t[37U];
  v37 =
    vb37
    +
      ((va37 + (vb37 ^ (vc37 ^ vd37)) + xk37 + ti37)
      << (u32)11U
      | (va37 + (vb37 ^ (vc37 ^ vd37)) + xk37 + ti37) >> (u32)21U);
  abcd[3U] = v37;
  va38 = abcd[2U];
  vb38 = abcd[3U];
  vc38 = abcd[0U];
  vd38 = abcd[1U];
  b38 = x + (u32)28U;
  u38 = load32_le(b38);
  xk38 = u38;
  ti38 = _t[38U];
  v38 =
    vb38
    +
      ((va38 + (vb38 ^ (vc38 ^ vd38)) + xk38 + ti38)
      << (u32)16U
      | (va38 + (vb38 ^ (vc38 ^ vd38)) + xk38 + ti38) >> (u32)16U);
  abcd[2U] = v38;
  va39 = abcd[1U];
  vb39 = abcd[2U];
  vc39 = abcd[3U];
  vd39 = abcd[0U];
  b39 = x + (u32)40U;
  u39 = load32_le(b39);
  xk39 = u39;
  ti39 = _t[39U];
  v39 =
    vb39
    +
      ((va39 + (vb39 ^ (vc39 ^ vd39)) + xk39 + ti39)
      << (u32)23U
      | (va39 + (vb39 ^ (vc39 ^ vd39)) + xk39 + ti39) >> (u32)9U);
  abcd[1U] = v39;
  va40 = abcd[0U];
  vb40 = abcd[1U];
  vc40 = abcd[2U];
  vd40 = abcd[3U];
  b40 = x + (u32)52U;
  u40 = load32_le(b40);
  xk40 = u40;
  ti40 = _t[40U];
  v40 =
    vb40
    +
      ((va40 + (vb40 ^ (vc40 ^ vd40)) + xk40 + ti40)
      << (u32)4U
      | (va40 + (vb40 ^ (vc40 ^ vd40)) + xk40 + ti40) >> (u32)28U);
  abcd[0U] = v40;
  va41 = abcd[3U];
  vb41 = abcd[0U];
  vc41 = abcd[1U];
  vd41 = abcd[2U];
  b41 = x;
  u41 = load32_le(b41);
  xk41 = u41;
  ti41 = _t[41U];
  v41 =
    vb41
    +
      ((va41 + (vb41 ^ (vc41 ^ vd41)) + xk41 + ti41)
      << (u32)11U
      | (va41 + (vb41 ^ (vc41 ^ vd41)) + xk41 + ti41) >> (u32)21U);
  abcd[3U] = v41;
  va42 = abcd[2U];
  vb42 = abcd[3U];
  vc42 = abcd[0U];
  vd42 = abcd[1U];
  b42 = x + (u32)12U;
  u42 = load32_le(b42);
  xk42 = u42;
  ti42 = _t[42U];
  v42 =
    vb42
    +
      ((va42 + (vb42 ^ (vc42 ^ vd42)) + xk42 + ti42)
      << (u32)16U
      | (va42 + (vb42 ^ (vc42 ^ vd42)) + xk42 + ti42) >> (u32)16U);
  abcd[2U] = v42;
  va43 = abcd[1U];
  vb43 = abcd[2U];
  vc43 = abcd[3U];
  vd43 = abcd[0U];
  b43 = x + (u32)24U;
  u43 = load32_le(b43);
  xk43 = u43;
  ti43 = _t[43U];
  v43 =
    vb43
    +
      ((va43 + (vb43 ^ (vc43 ^ vd43)) + xk43 + ti43)
      << (u32)23U
      | (va43 + (vb43 ^ (vc43 ^ vd43)) + xk43 + ti43) >> (u32)9U);
  abcd[1U] = v43;
  va44 = abcd[0U];
  vb44 = abcd[1U];
  vc44 = abcd[2U];
  vd44 = abcd[3U];
  b44 = x + (u32)36U;
  u44 = load32_le(b44);
  xk44 = u44;
  ti44 = _t[44U];
  v44 =
    vb44
    +
      ((va44 + (vb44 ^ (vc44 ^ vd44)) + xk44 + ti44)
      << (u32)4U
      | (va44 + (vb44 ^ (vc44 ^ vd44)) + xk44 + ti44) >> (u32)28U);
  abcd[0U] = v44;
  va45 = abcd[3U];
  vb45 = abcd[0U];
  vc45 = abcd[1U];
  vd45 = abcd[2U];
  b45 = x + (u32)48U;
  u45 = load32_le(b45);
  xk45 = u45;
  ti45 = _t[45U];
  v45 =
    vb45
    +
      ((va45 + (vb45 ^ (vc45 ^ vd45)) + xk45 + ti45)
      << (u32)11U
      | (va45 + (vb45 ^ (vc45 ^ vd45)) + xk45 + ti45) >> (u32)21U);
  abcd[3U] = v45;
  va46 = abcd[2U];
  vb46 = abcd[3U];
  vc46 = abcd[0U];
  vd46 = abcd[1U];
  b46 = x + (u32)60U;
  u46 = load32_le(b46);
  xk46 = u46;
  ti46 = _t[46U];
  v46 =
    vb46
    +
      ((va46 + (vb46 ^ (vc46 ^ vd46)) + xk46 + ti46)
      << (u32)16U
      | (va46 + (vb46 ^ (vc46 ^ vd46)) + xk46 + ti46) >> (u32)16U);
  abcd[2U] = v46;
  va47 = abcd[1U];
  vb47 = abcd[2U];
  vc47 = abcd[3U];
  vd47 = abcd[0U];
  b47 = x + (u32)8U;
  u47 = load32_le(b47);
  xk47 = u47;
  ti47 = _t[47U];
  v47 =
    vb47
    +
      ((va47 + (vb47 ^ (vc47 ^ vd47)) + xk47 + ti47)
      << (u32)23U
      | (va47 + (vb47 ^ (vc47 ^ vd47)) + xk47 + ti47) >> (u32)9U);
  abcd[1U] = v47;
  va48 = abcd[0U];
  vb48 = abcd[1U];
  vc48 = abcd[2U];
  vd48 = abcd[3U];
  b48 = x;
  u48 = load32_le(b48);
  xk48 = u48;
  ti48 = _t[48U];
  v48 =
    vb48
    +
      ((va48 + (vc48 ^ (vb48 | ~vd48)) + xk48 + ti48)
      << (u32)6U
      | (va48 + (vc48 ^ (vb48 | ~vd48)) + xk48 + ti48) >> (u32)26U);
  abcd[0U] = v48;
  va49 = abcd[3U];
  vb49 = abcd[0U];
  vc49 = abcd[1U];
  vd49 = abcd[2U];
  b49 = x + (u32)28U;
  u49 = load32_le(b49);
  xk49 = u49;
  ti49 = _t[49U];
  v49 =
    vb49
    +
      ((va49 + (vc49 ^ (vb49 | ~vd49)) + xk49 + ti49)
      << (u32)10U
      | (va49 + (vc49 ^ (vb49 | ~vd49)) + xk49 + ti49) >> (u32)22U);
  abcd[3U] = v49;
  va50 = abcd[2U];
  vb50 = abcd[3U];
  vc50 = abcd[0U];
  vd50 = abcd[1U];
  b50 = x + (u32)56U;
  u50 = load32_le(b50);
  xk50 = u50;
  ti50 = _t[50U];
  v50 =
    vb50
    +
      ((va50 + (vc50 ^ (vb50 | ~vd50)) + xk50 + ti50)
      << (u32)15U
      | (va50 + (vc50 ^ (vb50 | ~vd50)) + xk50 + ti50) >> (u32)17U);
  abcd[2U] = v50;
  va51 = abcd[1U];
  vb51 = abcd[2U];
  vc51 = abcd[3U];
  vd51 = abcd[0U];
  b51 = x + (u32)20U;
  u51 = load32_le(b51);
  xk51 = u51;
  ti51 = _t[51U];
  v51 =
    vb51
    +
      ((va51 + (vc51 ^ (vb51 | ~vd51)) + xk51 + ti51)
      << (u32)21U
      | (va51 + (vc51 ^ (vb51 | ~vd51)) + xk51 + ti51) >> (u32)11U);
  abcd[1U] = v51;
  va52 = abcd[0U];
  vb52 = abcd[1U];
  vc52 = abcd[2U];
  vd52 = abcd[3U];
  b52 = x + (u32)48U;
  u52 = load32_le(b52);
  xk52 = u52;
  ti52 = _t[52U];
  v52 =
    vb52
    +
      ((va52 + (vc52 ^ (vb52 | ~vd52)) + xk52 + ti52)
      << (u32)6U
      | (va52 + (vc52 ^ (vb52 | ~vd52)) + xk52 + ti52) >> (u32)26U);
  abcd[0U] = v52;
  va53 = abcd[3U];
  vb53 = abcd[0U];
  vc53 = abcd[1U];
  vd53 = abcd[2U];
  b53 = x + (u32)12U;
  u53 = load32_le(b53);
  xk53 = u53;
  ti53 = _t[53U];
  v53 =
    vb53
    +
      ((va53 + (vc53 ^ (vb53 | ~vd53)) + xk53 + ti53)
      << (u32)10U
      | (va53 + (vc53 ^ (vb53 | ~vd53)) + xk53 + ti53) >> (u32)22U);
  abcd[3U] = v53;
  va54 = abcd[2U];
  vb54 = abcd[3U];
  vc54 = abcd[0U];
  vd54 = abcd[1U];
  b54 = x + (u32)40U;
  u54 = load32_le(b54);
  xk54 = u54;
  ti54 = _t[54U];
  v54 =
    vb54
    +
      ((va54 + (vc54 ^ (vb54 | ~vd54)) + xk54 + ti54)
      << (u32)15U
      | (va54 + (vc54 ^ (vb54 | ~vd54)) + xk54 + ti54) >> (u32)17U);
  abcd[2U] = v54;
  va55 = abcd[1U];
  vb55 = abcd[2U];
  vc55 = abcd[3U];
  vd55 = abcd[0U];
  b55 = x + (u32)4U;
  u55 = load32_le(b55);
  xk55 = u55;
  ti55 = _t[55U];
  v55 =
    vb55
    +
      ((va55 + (vc55 ^ (vb55 | ~vd55)) + xk55 + ti55)
      << (u32)21U
      | (va55 + (vc55 ^ (vb55 | ~vd55)) + xk55 + ti55) >> (u32)11U);
  abcd[1U] = v55;
  va56 = abcd[0U];
  vb56 = abcd[1U];
  vc56 = abcd[2U];
  vd56 = abcd[3U];
  b56 = x + (u32)32U;
  u56 = load32_le(b56);
  xk56 = u56;
  ti56 = _t[56U];
  v56 =
    vb56
    +
      ((va56 + (vc56 ^ (vb56 | ~vd56)) + xk56 + ti56)
      << (u32)6U
      | (va56 + (vc56 ^ (vb56 | ~vd56)) + xk56 + ti56) >> (u32)26U);
  abcd[0U] = v56;
  va57 = abcd[3U];
  vb57 = abcd[0U];
  vc57 = abcd[1U];
  vd57 = abcd[2U];
  b57 = x + (u32)60U;
  u57 = load32_le(b57);
  xk57 = u57;
  ti57 = _t[57U];
  v57 =
    vb57
    +
      ((va57 + (vc57 ^ (vb57 | ~vd57)) + xk57 + ti57)
      << (u32)10U
      | (va57 + (vc57 ^ (vb57 | ~vd57)) + xk57 + ti57) >> (u32)22U);
  abcd[3U] = v57;
  va58 = abcd[2U];
  vb58 = abcd[3U];
  vc58 = abcd[0U];
  vd58 = abcd[1U];
  b58 = x + (u32)24U;
  u58 = load32_le(b58);
  xk58 = u58;
  ti58 = _t[58U];
  v58 =
    vb58
    +
      ((va58 + (vc58 ^ (vb58 | ~vd58)) + xk58 + ti58)
      << (u32)15U
      | (va58 + (vc58 ^ (vb58 | ~vd58)) + xk58 + ti58) >> (u32)17U);
  abcd[2U] = v58;
  va59 = abcd[1U];
  vb59 = abcd[2U];
  vc59 = abcd[3U];
  vd59 = abcd[0U];
  b59 = x + (u32)52U;
  u59 = load32_le(b59);
  xk59 = u59;
  ti59 = _t[59U];
  v59 =
    vb59
    +
      ((va59 + (vc59 ^ (vb59 | ~vd59)) + xk59 + ti59)
      << (u32)21U
      | (va59 + (vc59 ^ (vb59 | ~vd59)) + xk59 + ti59) >> (u32)11U);
  abcd[1U] = v59;
  va60 = abcd[0U];
  vb60 = abcd[1U];
  vc60 = abcd[2U];
  vd60 = abcd[3U];
  b60 = x + (u32)16U;
  u60 = load32_le(b60);
  xk60 = u60;
  ti60 = _t[60U];
  v60 =
    vb60
    +
      ((va60 + (vc60 ^ (vb60 | ~vd60)) + xk60 + ti60)
      << (u32)6U
      | (va60 + (vc60 ^ (vb60 | ~vd60)) + xk60 + ti60) >> (u32)26U);
  abcd[0U] = v60;
  va61 = abcd[3U];
  vb61 = abcd[0U];
  vc61 = abcd[1U];
  vd61 = abcd[2U];
  b61 = x + (u32)44U;
  u61 = load32_le(b61);
  xk61 = u61;
  ti61 = _t[61U];
  v61 =
    vb61
    +
      ((va61 + (vc61 ^ (vb61 | ~vd61)) + xk61 + ti61)
      << (u32)10U
      | (va61 + (vc61 ^ (vb61 | ~vd61)) + xk61 + ti61) >> (u32)22U);
  abcd[3U] = v61;
  va62 = abcd[2U];
  vb62 = abcd[3U];
  vc62 = abcd[0U];
  vd62 = abcd[1U];
  b62 = x + (u32)8U;
  u62 = load32_le(b62);
  xk62 = u62;
  ti62 = _t[62U];
  v62 =
    vb62
    +
      ((va62 + (vc62 ^ (vb62 | ~vd62)) + xk62 + ti62)
      << (u32)15U
      | (va62 + (vc62 ^ (vb62 | ~vd62)) + xk62 + ti62) >> (u32)17U);
  abcd[2U] = v62;
  va = abcd[1U];
  vb = abcd[2U];
  vc = abcd[3U];
  vd = abcd[0U];
  b63 = x + (u32)36U;
  u = load32_le(b63);
  xk = u;
  ti = _t[63U];
  v =
    vb
    +
      ((va + (vc ^ (vb | ~vd)) + xk + ti)
      << (u32)21U
      | (va + (vc ^ (vb | ~vd)) + xk + ti) >> (u32)11U);
  abcd[1U] = v;
  a = abcd[0U];
  b = abcd[1U];
  c = abcd[2U];
  d = abcd[3U];
  abcd[0U] = a + aa;
  abcd[1U] = b + bb;
  abcd[2U] = c + cc;
  abcd[3U] = d + dd;
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
  store64_le(dst3, len << (u32)3U);
}

static void legacy_finish(u32 *s, u8 *dst)
{
  u32 *uu____0 = s;
  u32 i;
  for (i = (u32)0U; i < (u32)4U; i++)
    store32_le(dst + i * (u32)4U, uu____0[i]);
}

void Hacl_Hash_MD5_legacy_update_multi(u32 *s, u8 *blocks, u32 n_blocks)
{
  u32 i;
  for (i = (u32)0U; i < n_blocks; i++)
  {
    u32 sz = (u32)64U;
    u8 *block = blocks + sz * i;
    legacy_update(s, block);
  }
}

void Hacl_Hash_MD5_legacy_update_last(u32 *s, u64 prev_len, u8 *input, u32 input_len)
{
  u32 blocks_n = input_len / (u32)64U;
  u32 blocks_len = blocks_n * (u32)64U;
  u8 *blocks = input;
  u32 rest_len = input_len - blocks_len;
  u8 *rest = input + blocks_len;
  u64 total_input_len;
  u32 pad_len;
  u32 tmp_len;
  Hacl_Hash_MD5_legacy_update_multi(s, blocks, blocks_n);
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
    Hacl_Hash_MD5_legacy_update_multi(s, tmp, tmp_len / (u32)64U);
  }
}

typedef u32 *___u32____;

void Hacl_Hash_MD5_legacy_hash(u8 *input, u32 input_len, u8 *dst)
{
  u32 scrut[4U] = { (u32)0x67452301U, (u32)0xefcdab89U, (u32)0x98badcfeU, (u32)0x10325476U };
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
    Hacl_Hash_MD5_legacy_update_multi(s, blocks, blocks_n);
    Hacl_Hash_MD5_legacy_update_last(s, (u64)blocks_len, rest, rest_len);
    legacy_finish(s, dst);
  }
}

