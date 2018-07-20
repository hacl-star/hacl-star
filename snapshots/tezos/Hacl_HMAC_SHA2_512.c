/* MIT License
 *
 * Copyright (c) 2016-2018 INRIA and Microsoft Corporation
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


#include "Hacl_HMAC_SHA2_512.h"

extern FStar_UInt128_uint128
FStar_UInt128_add(FStar_UInt128_uint128 x0, FStar_UInt128_uint128 x1);

extern FStar_UInt128_uint128 FStar_UInt128_shift_left(FStar_UInt128_uint128 x0, uint32_t x1);

extern FStar_UInt128_uint128 FStar_UInt128_uint64_to_uint128(uint64_t x0);

extern FStar_UInt128_uint128 FStar_UInt128_mul_wide(uint64_t x0, uint64_t x1);

extern void store128_be(uint8_t *x0, FStar_UInt128_uint128 x1);

static void
Hacl_Hash_Lib_LoadStore_uint64s_from_be_bytes(uint64_t *output, uint8_t *input, uint32_t len)
{
  for (uint32_t i = (uint32_t)0U; i < len; i = i + (uint32_t)1U)
  {
    uint8_t *x0 = input + (uint32_t)8U * i;
    uint64_t inputi = load64_be(x0);
    output[i] = inputi;
  }
}

static void
Hacl_Hash_Lib_LoadStore_uint64s_to_be_bytes(uint8_t *output, uint64_t *input, uint32_t len)
{
  for (uint32_t i = (uint32_t)0U; i < len; i = i + (uint32_t)1U)
  {
    uint64_t hd1 = input[i];
    uint8_t *x0 = output + (uint32_t)8U * i;
    store64_be(x0, hd1);
  }
}

static void Hacl_Impl_SHA2_512_assign_k(uint64_t *b)
{
  uint64_t *b_hd = b;
  uint64_t *b_tl = b + (uint32_t)1U;
  b_hd[0U] = (uint64_t)0x428a2f98d728ae22U;
  uint64_t *b_hd1 = b_tl;
  uint64_t *b_tl1 = b_tl + (uint32_t)1U;
  b_hd1[0U] = (uint64_t)0x7137449123ef65cdU;
  uint64_t *b_hd2 = b_tl1;
  uint64_t *b_tl2 = b_tl1 + (uint32_t)1U;
  b_hd2[0U] = (uint64_t)0xb5c0fbcfec4d3b2fU;
  uint64_t *b_hd3 = b_tl2;
  uint64_t *b_tl3 = b_tl2 + (uint32_t)1U;
  b_hd3[0U] = (uint64_t)0xe9b5dba58189dbbcU;
  uint64_t *b_hd4 = b_tl3;
  uint64_t *b_tl4 = b_tl3 + (uint32_t)1U;
  b_hd4[0U] = (uint64_t)0x3956c25bf348b538U;
  uint64_t *b_hd5 = b_tl4;
  uint64_t *b_tl5 = b_tl4 + (uint32_t)1U;
  b_hd5[0U] = (uint64_t)0x59f111f1b605d019U;
  uint64_t *b_hd6 = b_tl5;
  uint64_t *b_tl6 = b_tl5 + (uint32_t)1U;
  b_hd6[0U] = (uint64_t)0x923f82a4af194f9bU;
  uint64_t *b_hd7 = b_tl6;
  uint64_t *b_tl7 = b_tl6 + (uint32_t)1U;
  b_hd7[0U] = (uint64_t)0xab1c5ed5da6d8118U;
  uint64_t *b_hd8 = b_tl7;
  uint64_t *b_tl8 = b_tl7 + (uint32_t)1U;
  b_hd8[0U] = (uint64_t)0xd807aa98a3030242U;
  uint64_t *b_hd9 = b_tl8;
  uint64_t *b_tl9 = b_tl8 + (uint32_t)1U;
  b_hd9[0U] = (uint64_t)0x12835b0145706fbeU;
  uint64_t *b_hd10 = b_tl9;
  uint64_t *b_tl10 = b_tl9 + (uint32_t)1U;
  b_hd10[0U] = (uint64_t)0x243185be4ee4b28cU;
  uint64_t *b_hd11 = b_tl10;
  uint64_t *b_tl11 = b_tl10 + (uint32_t)1U;
  b_hd11[0U] = (uint64_t)0x550c7dc3d5ffb4e2U;
  uint64_t *b_hd12 = b_tl11;
  uint64_t *b_tl12 = b_tl11 + (uint32_t)1U;
  b_hd12[0U] = (uint64_t)0x72be5d74f27b896fU;
  uint64_t *b_hd13 = b_tl12;
  uint64_t *b_tl13 = b_tl12 + (uint32_t)1U;
  b_hd13[0U] = (uint64_t)0x80deb1fe3b1696b1U;
  uint64_t *b_hd14 = b_tl13;
  uint64_t *b_tl14 = b_tl13 + (uint32_t)1U;
  b_hd14[0U] = (uint64_t)0x9bdc06a725c71235U;
  uint64_t *b_hd15 = b_tl14;
  uint64_t *b_tl15 = b_tl14 + (uint32_t)1U;
  b_hd15[0U] = (uint64_t)0xc19bf174cf692694U;
  uint64_t *b_hd16 = b_tl15;
  uint64_t *b_tl16 = b_tl15 + (uint32_t)1U;
  b_hd16[0U] = (uint64_t)0xe49b69c19ef14ad2U;
  uint64_t *b_hd17 = b_tl16;
  uint64_t *b_tl17 = b_tl16 + (uint32_t)1U;
  b_hd17[0U] = (uint64_t)0xefbe4786384f25e3U;
  uint64_t *b_hd18 = b_tl17;
  uint64_t *b_tl18 = b_tl17 + (uint32_t)1U;
  b_hd18[0U] = (uint64_t)0x0fc19dc68b8cd5b5U;
  uint64_t *b_hd19 = b_tl18;
  uint64_t *b_tl19 = b_tl18 + (uint32_t)1U;
  b_hd19[0U] = (uint64_t)0x240ca1cc77ac9c65U;
  uint64_t *b_hd20 = b_tl19;
  uint64_t *b_tl20 = b_tl19 + (uint32_t)1U;
  b_hd20[0U] = (uint64_t)0x2de92c6f592b0275U;
  uint64_t *b_hd21 = b_tl20;
  uint64_t *b_tl21 = b_tl20 + (uint32_t)1U;
  b_hd21[0U] = (uint64_t)0x4a7484aa6ea6e483U;
  uint64_t *b_hd22 = b_tl21;
  uint64_t *b_tl22 = b_tl21 + (uint32_t)1U;
  b_hd22[0U] = (uint64_t)0x5cb0a9dcbd41fbd4U;
  uint64_t *b_hd23 = b_tl22;
  uint64_t *b_tl23 = b_tl22 + (uint32_t)1U;
  b_hd23[0U] = (uint64_t)0x76f988da831153b5U;
  uint64_t *b_hd24 = b_tl23;
  uint64_t *b_tl24 = b_tl23 + (uint32_t)1U;
  b_hd24[0U] = (uint64_t)0x983e5152ee66dfabU;
  uint64_t *b_hd25 = b_tl24;
  uint64_t *b_tl25 = b_tl24 + (uint32_t)1U;
  b_hd25[0U] = (uint64_t)0xa831c66d2db43210U;
  uint64_t *b_hd26 = b_tl25;
  uint64_t *b_tl26 = b_tl25 + (uint32_t)1U;
  b_hd26[0U] = (uint64_t)0xb00327c898fb213fU;
  uint64_t *b_hd27 = b_tl26;
  uint64_t *b_tl27 = b_tl26 + (uint32_t)1U;
  b_hd27[0U] = (uint64_t)0xbf597fc7beef0ee4U;
  uint64_t *b_hd28 = b_tl27;
  uint64_t *b_tl28 = b_tl27 + (uint32_t)1U;
  b_hd28[0U] = (uint64_t)0xc6e00bf33da88fc2U;
  uint64_t *b_hd29 = b_tl28;
  uint64_t *b_tl29 = b_tl28 + (uint32_t)1U;
  b_hd29[0U] = (uint64_t)0xd5a79147930aa725U;
  uint64_t *b_hd30 = b_tl29;
  uint64_t *b_tl30 = b_tl29 + (uint32_t)1U;
  b_hd30[0U] = (uint64_t)0x06ca6351e003826fU;
  uint64_t *b_hd31 = b_tl30;
  uint64_t *b_tl31 = b_tl30 + (uint32_t)1U;
  b_hd31[0U] = (uint64_t)0x142929670a0e6e70U;
  uint64_t *b_hd32 = b_tl31;
  uint64_t *b_tl32 = b_tl31 + (uint32_t)1U;
  b_hd32[0U] = (uint64_t)0x27b70a8546d22ffcU;
  uint64_t *b_hd33 = b_tl32;
  uint64_t *b_tl33 = b_tl32 + (uint32_t)1U;
  b_hd33[0U] = (uint64_t)0x2e1b21385c26c926U;
  uint64_t *b_hd34 = b_tl33;
  uint64_t *b_tl34 = b_tl33 + (uint32_t)1U;
  b_hd34[0U] = (uint64_t)0x4d2c6dfc5ac42aedU;
  uint64_t *b_hd35 = b_tl34;
  uint64_t *b_tl35 = b_tl34 + (uint32_t)1U;
  b_hd35[0U] = (uint64_t)0x53380d139d95b3dfU;
  uint64_t *b_hd36 = b_tl35;
  uint64_t *b_tl36 = b_tl35 + (uint32_t)1U;
  b_hd36[0U] = (uint64_t)0x650a73548baf63deU;
  uint64_t *b_hd37 = b_tl36;
  uint64_t *b_tl37 = b_tl36 + (uint32_t)1U;
  b_hd37[0U] = (uint64_t)0x766a0abb3c77b2a8U;
  uint64_t *b_hd38 = b_tl37;
  uint64_t *b_tl38 = b_tl37 + (uint32_t)1U;
  b_hd38[0U] = (uint64_t)0x81c2c92e47edaee6U;
  uint64_t *b_hd39 = b_tl38;
  uint64_t *b_tl39 = b_tl38 + (uint32_t)1U;
  b_hd39[0U] = (uint64_t)0x92722c851482353bU;
  uint64_t *b_hd40 = b_tl39;
  uint64_t *b_tl40 = b_tl39 + (uint32_t)1U;
  b_hd40[0U] = (uint64_t)0xa2bfe8a14cf10364U;
  uint64_t *b_hd41 = b_tl40;
  uint64_t *b_tl41 = b_tl40 + (uint32_t)1U;
  b_hd41[0U] = (uint64_t)0xa81a664bbc423001U;
  uint64_t *b_hd42 = b_tl41;
  uint64_t *b_tl42 = b_tl41 + (uint32_t)1U;
  b_hd42[0U] = (uint64_t)0xc24b8b70d0f89791U;
  uint64_t *b_hd43 = b_tl42;
  uint64_t *b_tl43 = b_tl42 + (uint32_t)1U;
  b_hd43[0U] = (uint64_t)0xc76c51a30654be30U;
  uint64_t *b_hd44 = b_tl43;
  uint64_t *b_tl44 = b_tl43 + (uint32_t)1U;
  b_hd44[0U] = (uint64_t)0xd192e819d6ef5218U;
  uint64_t *b_hd45 = b_tl44;
  uint64_t *b_tl45 = b_tl44 + (uint32_t)1U;
  b_hd45[0U] = (uint64_t)0xd69906245565a910U;
  uint64_t *b_hd46 = b_tl45;
  uint64_t *b_tl46 = b_tl45 + (uint32_t)1U;
  b_hd46[0U] = (uint64_t)0xf40e35855771202aU;
  uint64_t *b_hd47 = b_tl46;
  uint64_t *b_tl47 = b_tl46 + (uint32_t)1U;
  b_hd47[0U] = (uint64_t)0x106aa07032bbd1b8U;
  uint64_t *b_hd48 = b_tl47;
  uint64_t *b_tl48 = b_tl47 + (uint32_t)1U;
  b_hd48[0U] = (uint64_t)0x19a4c116b8d2d0c8U;
  uint64_t *b_hd49 = b_tl48;
  uint64_t *b_tl49 = b_tl48 + (uint32_t)1U;
  b_hd49[0U] = (uint64_t)0x1e376c085141ab53U;
  uint64_t *b_hd50 = b_tl49;
  uint64_t *b_tl50 = b_tl49 + (uint32_t)1U;
  b_hd50[0U] = (uint64_t)0x2748774cdf8eeb99U;
  uint64_t *b_hd51 = b_tl50;
  uint64_t *b_tl51 = b_tl50 + (uint32_t)1U;
  b_hd51[0U] = (uint64_t)0x34b0bcb5e19b48a8U;
  uint64_t *b_hd52 = b_tl51;
  uint64_t *b_tl52 = b_tl51 + (uint32_t)1U;
  b_hd52[0U] = (uint64_t)0x391c0cb3c5c95a63U;
  uint64_t *b_hd53 = b_tl52;
  uint64_t *b_tl53 = b_tl52 + (uint32_t)1U;
  b_hd53[0U] = (uint64_t)0x4ed8aa4ae3418acbU;
  uint64_t *b_hd54 = b_tl53;
  uint64_t *b_tl54 = b_tl53 + (uint32_t)1U;
  b_hd54[0U] = (uint64_t)0x5b9cca4f7763e373U;
  uint64_t *b_hd55 = b_tl54;
  uint64_t *b_tl55 = b_tl54 + (uint32_t)1U;
  b_hd55[0U] = (uint64_t)0x682e6ff3d6b2b8a3U;
  uint64_t *b_hd56 = b_tl55;
  uint64_t *b_tl56 = b_tl55 + (uint32_t)1U;
  b_hd56[0U] = (uint64_t)0x748f82ee5defb2fcU;
  uint64_t *b_hd57 = b_tl56;
  uint64_t *b_tl57 = b_tl56 + (uint32_t)1U;
  b_hd57[0U] = (uint64_t)0x78a5636f43172f60U;
  uint64_t *b_hd58 = b_tl57;
  uint64_t *b_tl58 = b_tl57 + (uint32_t)1U;
  b_hd58[0U] = (uint64_t)0x84c87814a1f0ab72U;
  uint64_t *b_hd59 = b_tl58;
  uint64_t *b_tl59 = b_tl58 + (uint32_t)1U;
  b_hd59[0U] = (uint64_t)0x8cc702081a6439ecU;
  uint64_t *b_hd60 = b_tl59;
  uint64_t *b_tl60 = b_tl59 + (uint32_t)1U;
  b_hd60[0U] = (uint64_t)0x90befffa23631e28U;
  uint64_t *b_hd61 = b_tl60;
  uint64_t *b_tl61 = b_tl60 + (uint32_t)1U;
  b_hd61[0U] = (uint64_t)0xa4506cebde82bde9U;
  uint64_t *b_hd62 = b_tl61;
  uint64_t *b_tl62 = b_tl61 + (uint32_t)1U;
  b_hd62[0U] = (uint64_t)0xbef9a3f7b2c67915U;
  uint64_t *b_hd63 = b_tl62;
  uint64_t *b_tl63 = b_tl62 + (uint32_t)1U;
  b_hd63[0U] = (uint64_t)0xc67178f2e372532bU;
  uint64_t *b_hd64 = b_tl63;
  uint64_t *b_tl64 = b_tl63 + (uint32_t)1U;
  b_hd64[0U] = (uint64_t)0xca273eceea26619cU;
  uint64_t *b_hd65 = b_tl64;
  uint64_t *b_tl65 = b_tl64 + (uint32_t)1U;
  b_hd65[0U] = (uint64_t)0xd186b8c721c0c207U;
  uint64_t *b_hd66 = b_tl65;
  uint64_t *b_tl66 = b_tl65 + (uint32_t)1U;
  b_hd66[0U] = (uint64_t)0xeada7dd6cde0eb1eU;
  uint64_t *b_hd67 = b_tl66;
  uint64_t *b_tl67 = b_tl66 + (uint32_t)1U;
  b_hd67[0U] = (uint64_t)0xf57d4f7fee6ed178U;
  uint64_t *b_hd68 = b_tl67;
  uint64_t *b_tl68 = b_tl67 + (uint32_t)1U;
  b_hd68[0U] = (uint64_t)0x06f067aa72176fbaU;
  uint64_t *b_hd69 = b_tl68;
  uint64_t *b_tl69 = b_tl68 + (uint32_t)1U;
  b_hd69[0U] = (uint64_t)0x0a637dc5a2c898a6U;
  uint64_t *b_hd70 = b_tl69;
  uint64_t *b_tl70 = b_tl69 + (uint32_t)1U;
  b_hd70[0U] = (uint64_t)0x113f9804bef90daeU;
  uint64_t *b_hd71 = b_tl70;
  uint64_t *b_tl71 = b_tl70 + (uint32_t)1U;
  b_hd71[0U] = (uint64_t)0x1b710b35131c471bU;
  uint64_t *b_hd72 = b_tl71;
  uint64_t *b_tl72 = b_tl71 + (uint32_t)1U;
  b_hd72[0U] = (uint64_t)0x28db77f523047d84U;
  uint64_t *b_hd73 = b_tl72;
  uint64_t *b_tl73 = b_tl72 + (uint32_t)1U;
  b_hd73[0U] = (uint64_t)0x32caab7b40c72493U;
  uint64_t *b_hd74 = b_tl73;
  uint64_t *b_tl74 = b_tl73 + (uint32_t)1U;
  b_hd74[0U] = (uint64_t)0x3c9ebe0a15c9bebcU;
  uint64_t *b_hd75 = b_tl74;
  uint64_t *b_tl75 = b_tl74 + (uint32_t)1U;
  b_hd75[0U] = (uint64_t)0x431d67c49c100d4cU;
  uint64_t *b_hd76 = b_tl75;
  uint64_t *b_tl76 = b_tl75 + (uint32_t)1U;
  b_hd76[0U] = (uint64_t)0x4cc5d4becb3e42b6U;
  uint64_t *b_hd77 = b_tl76;
  uint64_t *b_tl77 = b_tl76 + (uint32_t)1U;
  b_hd77[0U] = (uint64_t)0x597f299cfc657e2aU;
  uint64_t *b_hd78 = b_tl77;
  uint64_t *b_tl78 = b_tl77 + (uint32_t)1U;
  b_hd78[0U] = (uint64_t)0x5fcb6fab3ad6faecU;
  uint64_t *b_hd79 = b_tl78;
  b_hd79[0U] = (uint64_t)0x6c44198c4a475817U;
}

static void Hacl_Impl_SHA2_512_constants_set_k(uint64_t *k1)
{
  Hacl_Impl_SHA2_512_assign_k(k1);
}

static void Hacl_Impl_SHA2_512_assign_h0(uint64_t *b)
{
  uint64_t *b_hd = b;
  uint64_t *b_tl = b + (uint32_t)1U;
  b_hd[0U] = (uint64_t)0x6a09e667f3bcc908U;
  uint64_t *b_hd1 = b_tl;
  uint64_t *b_tl1 = b_tl + (uint32_t)1U;
  b_hd1[0U] = (uint64_t)0xbb67ae8584caa73bU;
  uint64_t *b_hd2 = b_tl1;
  uint64_t *b_tl2 = b_tl1 + (uint32_t)1U;
  b_hd2[0U] = (uint64_t)0x3c6ef372fe94f82bU;
  uint64_t *b_hd3 = b_tl2;
  uint64_t *b_tl3 = b_tl2 + (uint32_t)1U;
  b_hd3[0U] = (uint64_t)0xa54ff53a5f1d36f1U;
  uint64_t *b_hd4 = b_tl3;
  uint64_t *b_tl4 = b_tl3 + (uint32_t)1U;
  b_hd4[0U] = (uint64_t)0x510e527fade682d1U;
  uint64_t *b_hd5 = b_tl4;
  uint64_t *b_tl5 = b_tl4 + (uint32_t)1U;
  b_hd5[0U] = (uint64_t)0x9b05688c2b3e6c1fU;
  uint64_t *b_hd6 = b_tl5;
  uint64_t *b_tl6 = b_tl5 + (uint32_t)1U;
  b_hd6[0U] = (uint64_t)0x1f83d9abfb41bd6bU;
  uint64_t *b_hd7 = b_tl6;
  b_hd7[0U] = (uint64_t)0x5be0cd19137e2179U;
}

static void Hacl_Impl_SHA2_512_init(uint64_t *state)
{
  uint64_t *n1 = state + (uint32_t)168U;
  uint64_t *k1 = state;
  uint64_t *h_01 = state + (uint32_t)160U;
  Hacl_Impl_SHA2_512_constants_set_k(k1);
  Hacl_Impl_SHA2_512_assign_h0(h_01);
  n1[0U] = (uint64_t)0U;
}

static void Hacl_Impl_SHA2_512_update(uint64_t *state, uint8_t *data)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)16U);
  uint64_t data_w[16U];
  for (uint32_t _i = 0U; _i < (uint32_t)16U; ++_i)
    data_w[_i] = (uint64_t)(uint32_t)0U;
  Hacl_Hash_Lib_LoadStore_uint64s_from_be_bytes(data_w, data, (uint32_t)16U);
  uint64_t *hash_w = state + (uint32_t)160U;
  uint64_t *ws_w = state + (uint32_t)80U;
  uint64_t *k_w = state;
  uint64_t *counter_w = state + (uint32_t)168U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
  {
    uint64_t b = data_w[i];
    ws_w[i] = b;
  }
  for (uint32_t i = (uint32_t)16U; i < (uint32_t)80U; i = i + (uint32_t)1U)
  {
    uint64_t t16 = ws_w[i - (uint32_t)16U];
    uint64_t t15 = ws_w[i - (uint32_t)15U];
    uint64_t t7 = ws_w[i - (uint32_t)7U];
    uint64_t t2 = ws_w[i - (uint32_t)2U];
    ws_w[i] =
      ((t2 >> (uint32_t)19U | t2 << ((uint32_t)64U - (uint32_t)19U))
      ^ ((t2 >> (uint32_t)61U | t2 << ((uint32_t)64U - (uint32_t)61U)) ^ t2 >> (uint32_t)6U))
      +
        t7
        +
          ((t15 >> (uint32_t)1U | t15 << ((uint32_t)64U - (uint32_t)1U))
          ^ ((t15 >> (uint32_t)8U | t15 << ((uint32_t)64U - (uint32_t)8U)) ^ t15 >> (uint32_t)7U))
          + t16;
  }
  uint64_t hash_0[8U] = { 0U };
  memcpy(hash_0, hash_w, (uint32_t)8U * sizeof hash_w[0U]);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)80U; i = i + (uint32_t)1U)
  {
    uint64_t a = hash_0[0U];
    uint64_t b = hash_0[1U];
    uint64_t c = hash_0[2U];
    uint64_t d = hash_0[3U];
    uint64_t e = hash_0[4U];
    uint64_t f = hash_0[5U];
    uint64_t g = hash_0[6U];
    uint64_t h = hash_0[7U];
    uint64_t k_t = k_w[i];
    uint64_t ws_t = ws_w[i];
    uint64_t
    t1 =
      h
      +
        ((e >> (uint32_t)14U | e << ((uint32_t)64U - (uint32_t)14U))
        ^
          ((e >> (uint32_t)18U | e << ((uint32_t)64U - (uint32_t)18U))
          ^ (e >> (uint32_t)41U | e << ((uint32_t)64U - (uint32_t)41U))))
      + ((e & f) ^ (~e & g))
      + k_t
      + ws_t;
    uint64_t
    t2 =
      ((a >> (uint32_t)28U | a << ((uint32_t)64U - (uint32_t)28U))
      ^
        ((a >> (uint32_t)34U | a << ((uint32_t)64U - (uint32_t)34U))
        ^ (a >> (uint32_t)39U | a << ((uint32_t)64U - (uint32_t)39U))))
      + ((a & b) ^ ((a & c) ^ (b & c)));
    uint64_t x1 = t1 + t2;
    uint64_t x5 = d + t1;
    uint64_t *p1 = hash_0;
    uint64_t *p2 = hash_0 + (uint32_t)4U;
    p1[0U] = x1;
    p1[1U] = a;
    p1[2U] = b;
    p1[3U] = c;
    p2[0U] = x5;
    p2[1U] = e;
    p2[2U] = f;
    p2[3U] = g;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    uint64_t xi = hash_w[i];
    uint64_t yi = hash_0[i];
    hash_w[i] = xi + yi;
  }
  uint64_t c0 = counter_w[0U];
  uint64_t one1 = (uint64_t)(uint32_t)1U;
  counter_w[0U] = c0 + one1;
}

static void Hacl_Impl_SHA2_512_update_multi(uint64_t *state, uint8_t *data, uint32_t n1)
{
  for (uint32_t i = (uint32_t)0U; i < n1; i = i + (uint32_t)1U)
  {
    uint8_t *b = data + i * (uint32_t)128U;
    Hacl_Impl_SHA2_512_update(state, b);
  }
}

static void Hacl_Impl_SHA2_512_update_last(uint64_t *state, uint8_t *data, uint32_t len)
{
  uint8_t blocks[256U] = { 0U };
  uint32_t nb;
  if (len < (uint32_t)112U)
    nb = (uint32_t)1U;
  else
    nb = (uint32_t)2U;
  uint8_t *final_blocks;
  if (len < (uint32_t)112U)
    final_blocks = blocks + (uint32_t)128U;
  else
    final_blocks = blocks;
  memcpy(final_blocks, data, len * sizeof data[0U]);
  uint64_t n1 = state[168U];
  uint8_t *padding = final_blocks + len;
  FStar_UInt128_uint128
  l0 = FStar_UInt128_mul_wide((uint64_t)(uint32_t)n1, (uint64_t)(uint32_t)128U);
  FStar_UInt128_uint128 l1 = FStar_UInt128_uint64_to_uint128((uint64_t)len);
  FStar_UInt128_uint128
  encodedlen = FStar_UInt128_shift_left(FStar_UInt128_add(l0, l1), (uint32_t)3U);
  uint32_t pad0len = ((uint32_t)256U - (len + (uint32_t)16U + (uint32_t)1U)) % (uint32_t)128U;
  uint8_t *buf1 = padding;
  uint8_t *buf2 = padding + (uint32_t)1U + pad0len;
  buf1[0U] = (uint8_t)0x80U;
  store128_be(buf2, encodedlen);
  Hacl_Impl_SHA2_512_update_multi(state, final_blocks, nb);
}

static void Hacl_Impl_SHA2_512_finish(uint64_t *state, uint8_t *hash1)
{
  uint64_t *hash_w = state + (uint32_t)160U;
  Hacl_Hash_Lib_LoadStore_uint64s_to_be_bytes(hash1, hash_w, (uint32_t)8U);
}

static void Hacl_Impl_SHA2_512_hash(uint8_t *hash1, uint8_t *input, uint32_t len)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)169U);
  uint64_t state[169U];
  for (uint32_t _i = 0U; _i < (uint32_t)169U; ++_i)
    state[_i] = (uint64_t)(uint32_t)0U;
  uint32_t n1 = len / (uint32_t)128U;
  uint32_t r = len % (uint32_t)128U;
  uint8_t *input_blocks = input;
  uint8_t *input_last = input + n1 * (uint32_t)128U;
  Hacl_Impl_SHA2_512_init(state);
  Hacl_Impl_SHA2_512_update_multi(state, input_blocks, n1);
  Hacl_Impl_SHA2_512_update_last(state, input_last, r);
  Hacl_Impl_SHA2_512_finish(state, hash1);
}

static void Hacl_Impl_HMAC_SHA2_512_xor_bytes_inplace(uint8_t *a, uint8_t *b, uint32_t len)
{
  for (uint32_t i = (uint32_t)0U; i < len; i = i + (uint32_t)1U)
  {
    uint8_t xi = a[i];
    uint8_t yi = b[i];
    a[i] = xi ^ yi;
  }
}

static void
Hacl_Impl_HMAC_SHA2_512_hmac_core(uint8_t *mac, uint8_t *key, uint8_t *data, uint32_t len)
{
  uint8_t ipad[128U];
  for (uint32_t _i = 0U; _i < (uint32_t)128U; ++_i)
    ipad[_i] = (uint8_t)0x36U;
  uint8_t opad[128U];
  for (uint32_t _i = 0U; _i < (uint32_t)128U; ++_i)
    opad[_i] = (uint8_t)0x5cU;
  Hacl_Impl_HMAC_SHA2_512_xor_bytes_inplace(ipad, key, (uint32_t)128U);
  uint32_t state0[169U] = { 0U };
  uint32_t n0 = len / (uint32_t)128U;
  uint32_t r0 = len % (uint32_t)128U;
  uint8_t *blocks0 = data;
  uint8_t *last0 = data + n0 * (uint32_t)128U;
  Hacl_Impl_SHA2_512_init((uint64_t *)state0);
  Hacl_Impl_SHA2_512_update((uint64_t *)state0, ipad);
  Hacl_Impl_SHA2_512_update_multi((uint64_t *)state0, blocks0, n0);
  Hacl_Impl_SHA2_512_update_last((uint64_t *)state0, last0, r0);
  uint8_t *hash0 = ipad;
  Hacl_Impl_SHA2_512_finish((uint64_t *)state0, hash0);
  uint8_t *s4 = ipad;
  Hacl_Impl_HMAC_SHA2_512_xor_bytes_inplace(opad, key, (uint32_t)128U);
  uint32_t state1[169U] = { 0U };
  Hacl_Impl_SHA2_512_init((uint64_t *)state1);
  Hacl_Impl_SHA2_512_update((uint64_t *)state1, opad);
  Hacl_Impl_SHA2_512_update_last((uint64_t *)state1, s4, (uint32_t)64U);
  Hacl_Impl_SHA2_512_finish((uint64_t *)state1, mac);
}

static void
Hacl_Impl_HMAC_SHA2_512_hmac(
  uint8_t *mac,
  uint8_t *key,
  uint32_t keylen,
  uint8_t *data,
  uint32_t datalen
)
{
  uint8_t nkey[128U];
  for (uint32_t _i = 0U; _i < (uint32_t)128U; ++_i)
    nkey[_i] = (uint8_t)0x00U;
  if (keylen <= (uint32_t)128U)
    memcpy(nkey, key, keylen * sizeof key[0U]);
  else
  {
    uint8_t *nkey0 = nkey;
    Hacl_Impl_SHA2_512_hash(nkey0, key, keylen);
  }
  Hacl_Impl_HMAC_SHA2_512_hmac_core(mac, nkey, data, datalen);
}

void Hacl_HMAC_SHA2_512_hmac_core(uint8_t *mac, uint8_t *key, uint8_t *data, uint32_t len)
{
  Hacl_Impl_HMAC_SHA2_512_hmac_core(mac, key, data, len);
}

void
Hacl_HMAC_SHA2_512_hmac(
  uint8_t *mac,
  uint8_t *key,
  uint32_t keylen,
  uint8_t *data,
  uint32_t datalen
)
{
  Hacl_Impl_HMAC_SHA2_512_hmac(mac, key, keylen, data, datalen);
}

