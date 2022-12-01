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


#include "Hacl_Test_CSHAKE.h"



extern void Hacl_Impl_SHA3_state_permute(uint64_t *s);

extern void
Hacl_Impl_SHA3_absorb(
  uint64_t *s,
  uint32_t rateInBytes,
  uint32_t inputByteLen,
  uint8_t *input,
  uint8_t delimitedSuffix
);

extern void
Hacl_Impl_SHA3_squeeze(
  uint64_t *s,
  uint32_t rateInBytes,
  uint32_t outputByteLen,
  uint8_t *output
);

extern void C_String_print(C_String_t uu___);

extern bool
Lib_PrintBuffer_result_compare_display(uint32_t len, const uint8_t *buf0, const uint8_t *buf1);

static void
test_cshake128(
  uint32_t msg_len,
  uint8_t *msg,
  uint16_t ctr,
  uint32_t out_len,
  uint8_t *expected
)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), out_len);
  uint8_t test[out_len];
  memset(test, 0U, out_len * sizeof (uint8_t));
  uint64_t s[25U] = { 0U };
  s[0U] = (uint64_t)0x10010001a801U | (uint64_t)ctr << (uint32_t)48U;
  Hacl_Impl_SHA3_state_permute(s);
  Hacl_Impl_SHA3_absorb(s, (uint32_t)168U, msg_len, msg, (uint8_t)0x04U);
  Hacl_Impl_SHA3_squeeze(s, (uint32_t)168U, out_len, test);
  if (!Lib_PrintBuffer_result_compare_display(out_len, test, expected))
  {
    exit((int32_t)255);
  }
}

static uint8_t
test1_plaintext[16U] =
  {
    (uint8_t)0x61U, (uint8_t)0x62U, (uint8_t)0x63U, (uint8_t)0x64U, (uint8_t)0x65U, (uint8_t)0x66U,
    (uint8_t)0x67U, (uint8_t)0x68U, (uint8_t)0x62U, (uint8_t)0x63U, (uint8_t)0x64U, (uint8_t)0x65U,
    (uint8_t)0x66U, (uint8_t)0x67U, (uint8_t)0x68U, (uint8_t)0x69U
  };

static uint8_t
test1_expected[64U] =
  {
    (uint8_t)0x89U, (uint8_t)0x2eU, (uint8_t)0xd8U, (uint8_t)0xb5U, (uint8_t)0x1aU, (uint8_t)0xecU,
    (uint8_t)0x70U, (uint8_t)0x3fU, (uint8_t)0xdaU, (uint8_t)0x4bU, (uint8_t)0x40U, (uint8_t)0x0eU,
    (uint8_t)0x93U, (uint8_t)0xa4U, (uint8_t)0x94U, (uint8_t)0x56U, (uint8_t)0xd3U, (uint8_t)0x28U,
    (uint8_t)0xdfU, (uint8_t)0x46U, (uint8_t)0x0dU, (uint8_t)0x35U, (uint8_t)0x80U, (uint8_t)0x2aU,
    (uint8_t)0x01U, (uint8_t)0xbfU, (uint8_t)0xcfU, (uint8_t)0xa7U, (uint8_t)0x3dU, (uint8_t)0xa3U,
    (uint8_t)0xd0U, (uint8_t)0xb1U, (uint8_t)0xb4U, (uint8_t)0x87U, (uint8_t)0x94U, (uint8_t)0x2dU,
    (uint8_t)0xe9U, (uint8_t)0x34U, (uint8_t)0x8bU, (uint8_t)0x9fU, (uint8_t)0xa0U, (uint8_t)0xbeU,
    (uint8_t)0xb0U, (uint8_t)0xedU, (uint8_t)0x09U, (uint8_t)0x29U, (uint8_t)0x5bU, (uint8_t)0x96U,
    (uint8_t)0x9bU, (uint8_t)0x2fU, (uint8_t)0x14U, (uint8_t)0x24U, (uint8_t)0xf8U, (uint8_t)0x6aU,
    (uint8_t)0x4aU, (uint8_t)0x39U, (uint8_t)0xc5U, (uint8_t)0x2eU, (uint8_t)0xb3U, (uint8_t)0xc5U,
    (uint8_t)0xe2U, (uint8_t)0xb2U, (uint8_t)0x23U, (uint8_t)0x6fU
  };

exit_code main()
{
  C_String_print("\nTEST 1. SHA3\n");
  test_cshake128((uint32_t)16U, test1_plaintext, (uint16_t)2U, (uint32_t)64U, test1_expected);
  return EXIT_SUCCESS;
}

