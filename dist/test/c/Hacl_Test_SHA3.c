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


#include "Hacl_Test_SHA3.h"



extern void
Hacl_Impl_SHA3_keccak(
  uint32_t rate,
  uint32_t capacity,
  uint32_t inputByteLen,
  uint8_t *input,
  uint8_t delimitedSuffix,
  uint32_t outputByteLen,
  uint8_t *output
);

extern void C_String_print(C_String_t uu___);

static void
shake128_hacl(uint32_t inputByteLen, uint8_t *input, uint32_t outputByteLen, uint8_t *output)
{
  Hacl_Impl_SHA3_keccak((uint32_t)1344U,
    (uint32_t)256U,
    inputByteLen,
    input,
    (uint8_t)0x1FU,
    outputByteLen,
    output);
}

static void
shake256_hacl(uint32_t inputByteLen, uint8_t *input, uint32_t outputByteLen, uint8_t *output)
{
  Hacl_Impl_SHA3_keccak((uint32_t)1088U,
    (uint32_t)512U,
    inputByteLen,
    input,
    (uint8_t)0x1FU,
    outputByteLen,
    output);
}

static void sha3_224(uint32_t inputByteLen, uint8_t *input, uint8_t *output)
{
  Hacl_Impl_SHA3_keccak((uint32_t)1152U,
    (uint32_t)448U,
    inputByteLen,
    input,
    (uint8_t)0x06U,
    (uint32_t)28U,
    output);
}

static void sha3_256(uint32_t inputByteLen, uint8_t *input, uint8_t *output)
{
  Hacl_Impl_SHA3_keccak((uint32_t)1088U,
    (uint32_t)512U,
    inputByteLen,
    input,
    (uint8_t)0x06U,
    (uint32_t)32U,
    output);
}

static void sha3_384(uint32_t inputByteLen, uint8_t *input, uint8_t *output)
{
  Hacl_Impl_SHA3_keccak((uint32_t)832U,
    (uint32_t)768U,
    inputByteLen,
    input,
    (uint8_t)0x06U,
    (uint32_t)48U,
    output);
}

static void sha3_512(uint32_t inputByteLen, uint8_t *input, uint8_t *output)
{
  Hacl_Impl_SHA3_keccak((uint32_t)576U,
    (uint32_t)1024U,
    inputByteLen,
    input,
    (uint8_t)0x06U,
    (uint32_t)64U,
    output);
}

extern bool
Lib_PrintBuffer_result_compare_display(uint32_t len, const uint8_t *buf0, const uint8_t *buf1);

static void
test_sha3(
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
  sha3_224(msg_len, msg, test224);
  sha3_256(msg_len, msg, test256);
  sha3_384(msg_len, msg, test384);
  sha3_512(msg_len, msg, test512);
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

static void test_shake128(uint32_t msg_len, uint8_t *msg, uint32_t out_len, uint8_t *expected)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), out_len);
  uint8_t test[out_len];
  memset(test, 0U, out_len * sizeof (uint8_t));
  shake128_hacl(msg_len, msg, out_len, test);
  if (!Lib_PrintBuffer_result_compare_display(out_len, test, expected))
  {
    exit((int32_t)255);
  }
}

static void test_shake256(uint32_t msg_len, uint8_t *msg, uint32_t out_len, uint8_t *expected)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), out_len);
  uint8_t test[out_len];
  memset(test, 0U, out_len * sizeof (uint8_t));
  shake256_hacl(msg_len, msg, out_len, test);
  if (!Lib_PrintBuffer_result_compare_display(out_len, test, expected))
  {
    exit((int32_t)255);
  }
}

static uint8_t test1_plaintext[0U] = {  };

static uint8_t
test1_expected_sha3_224[28U] =
  {
    (uint8_t)0x6bU, (uint8_t)0x4eU, (uint8_t)0x03U, (uint8_t)0x42U, (uint8_t)0x36U, (uint8_t)0x67U,
    (uint8_t)0xdbU, (uint8_t)0xb7U, (uint8_t)0x3bU, (uint8_t)0x6eU, (uint8_t)0x15U, (uint8_t)0x45U,
    (uint8_t)0x4fU, (uint8_t)0x0eU, (uint8_t)0xb1U, (uint8_t)0xabU, (uint8_t)0xd4U, (uint8_t)0x59U,
    (uint8_t)0x7fU, (uint8_t)0x9aU, (uint8_t)0x1bU, (uint8_t)0x07U, (uint8_t)0x8eU, (uint8_t)0x3fU,
    (uint8_t)0x5bU, (uint8_t)0x5aU, (uint8_t)0x6bU, (uint8_t)0xc7U
  };

static uint8_t
test1_expected_sha3_256[32U] =
  {
    (uint8_t)0xa7U, (uint8_t)0xffU, (uint8_t)0xc6U, (uint8_t)0xf8U, (uint8_t)0xbfU, (uint8_t)0x1eU,
    (uint8_t)0xd7U, (uint8_t)0x66U, (uint8_t)0x51U, (uint8_t)0xc1U, (uint8_t)0x47U, (uint8_t)0x56U,
    (uint8_t)0xa0U, (uint8_t)0x61U, (uint8_t)0xd6U, (uint8_t)0x62U, (uint8_t)0xf5U, (uint8_t)0x80U,
    (uint8_t)0xffU, (uint8_t)0x4dU, (uint8_t)0xe4U, (uint8_t)0x3bU, (uint8_t)0x49U, (uint8_t)0xfaU,
    (uint8_t)0x82U, (uint8_t)0xd8U, (uint8_t)0x0aU, (uint8_t)0x4bU, (uint8_t)0x80U, (uint8_t)0xf8U,
    (uint8_t)0x43U, (uint8_t)0x4aU
  };

static uint8_t
test1_expected_sha3_384[48U] =
  {
    (uint8_t)0x0cU, (uint8_t)0x63U, (uint8_t)0xa7U, (uint8_t)0x5bU, (uint8_t)0x84U, (uint8_t)0x5eU,
    (uint8_t)0x4fU, (uint8_t)0x7dU, (uint8_t)0x01U, (uint8_t)0x10U, (uint8_t)0x7dU, (uint8_t)0x85U,
    (uint8_t)0x2eU, (uint8_t)0x4cU, (uint8_t)0x24U, (uint8_t)0x85U, (uint8_t)0xc5U, (uint8_t)0x1aU,
    (uint8_t)0x50U, (uint8_t)0xaaU, (uint8_t)0xaaU, (uint8_t)0x94U, (uint8_t)0xfcU, (uint8_t)0x61U,
    (uint8_t)0x99U, (uint8_t)0x5eU, (uint8_t)0x71U, (uint8_t)0xbbU, (uint8_t)0xeeU, (uint8_t)0x98U,
    (uint8_t)0x3aU, (uint8_t)0x2aU, (uint8_t)0xc3U, (uint8_t)0x71U, (uint8_t)0x38U, (uint8_t)0x31U,
    (uint8_t)0x26U, (uint8_t)0x4aU, (uint8_t)0xdbU, (uint8_t)0x47U, (uint8_t)0xfbU, (uint8_t)0x6bU,
    (uint8_t)0xd1U, (uint8_t)0xe0U, (uint8_t)0x58U, (uint8_t)0xd5U, (uint8_t)0xf0U, (uint8_t)0x04U
  };

static uint8_t
test1_expected_sha3_512[64U] =
  {
    (uint8_t)0xa6U, (uint8_t)0x9fU, (uint8_t)0x73U, (uint8_t)0xccU, (uint8_t)0xa2U, (uint8_t)0x3aU,
    (uint8_t)0x9aU, (uint8_t)0xc5U, (uint8_t)0xc8U, (uint8_t)0xb5U, (uint8_t)0x67U, (uint8_t)0xdcU,
    (uint8_t)0x18U, (uint8_t)0x5aU, (uint8_t)0x75U, (uint8_t)0x6eU, (uint8_t)0x97U, (uint8_t)0xc9U,
    (uint8_t)0x82U, (uint8_t)0x16U, (uint8_t)0x4fU, (uint8_t)0xe2U, (uint8_t)0x58U, (uint8_t)0x59U,
    (uint8_t)0xe0U, (uint8_t)0xd1U, (uint8_t)0xdcU, (uint8_t)0xc1U, (uint8_t)0x47U, (uint8_t)0x5cU,
    (uint8_t)0x80U, (uint8_t)0xa6U, (uint8_t)0x15U, (uint8_t)0xb2U, (uint8_t)0x12U, (uint8_t)0x3aU,
    (uint8_t)0xf1U, (uint8_t)0xf5U, (uint8_t)0xf9U, (uint8_t)0x4cU, (uint8_t)0x11U, (uint8_t)0xe3U,
    (uint8_t)0xe9U, (uint8_t)0x40U, (uint8_t)0x2cU, (uint8_t)0x3aU, (uint8_t)0xc5U, (uint8_t)0x58U,
    (uint8_t)0xf5U, (uint8_t)0x00U, (uint8_t)0x19U, (uint8_t)0x9dU, (uint8_t)0x95U, (uint8_t)0xb6U,
    (uint8_t)0xd3U, (uint8_t)0xe3U, (uint8_t)0x01U, (uint8_t)0x75U, (uint8_t)0x85U, (uint8_t)0x86U,
    (uint8_t)0x28U, (uint8_t)0x1dU, (uint8_t)0xcdU, (uint8_t)0x26U
  };

static uint8_t test2_plaintext[3U] = { (uint8_t)0x61U, (uint8_t)0x62U, (uint8_t)0x63U };

static uint8_t
test2_expected_sha3_224[28U] =
  {
    (uint8_t)0xe6U, (uint8_t)0x42U, (uint8_t)0x82U, (uint8_t)0x4cU, (uint8_t)0x3fU, (uint8_t)0x8cU,
    (uint8_t)0xf2U, (uint8_t)0x4aU, (uint8_t)0xd0U, (uint8_t)0x92U, (uint8_t)0x34U, (uint8_t)0xeeU,
    (uint8_t)0x7dU, (uint8_t)0x3cU, (uint8_t)0x76U, (uint8_t)0x6fU, (uint8_t)0xc9U, (uint8_t)0xa3U,
    (uint8_t)0xa5U, (uint8_t)0x16U, (uint8_t)0x8dU, (uint8_t)0x0cU, (uint8_t)0x94U, (uint8_t)0xadU,
    (uint8_t)0x73U, (uint8_t)0xb4U, (uint8_t)0x6fU, (uint8_t)0xdfU
  };

static uint8_t
test2_expected_sha3_256[32U] =
  {
    (uint8_t)0x3aU, (uint8_t)0x98U, (uint8_t)0x5dU, (uint8_t)0xa7U, (uint8_t)0x4fU, (uint8_t)0xe2U,
    (uint8_t)0x25U, (uint8_t)0xb2U, (uint8_t)0x04U, (uint8_t)0x5cU, (uint8_t)0x17U, (uint8_t)0x2dU,
    (uint8_t)0x6bU, (uint8_t)0xd3U, (uint8_t)0x90U, (uint8_t)0xbdU, (uint8_t)0x85U, (uint8_t)0x5fU,
    (uint8_t)0x08U, (uint8_t)0x6eU, (uint8_t)0x3eU, (uint8_t)0x9dU, (uint8_t)0x52U, (uint8_t)0x5bU,
    (uint8_t)0x46U, (uint8_t)0xbfU, (uint8_t)0xe2U, (uint8_t)0x45U, (uint8_t)0x11U, (uint8_t)0x43U,
    (uint8_t)0x15U, (uint8_t)0x32U
  };

static uint8_t
test2_expected_sha3_384[48U] =
  {
    (uint8_t)0xecU, (uint8_t)0x01U, (uint8_t)0x49U, (uint8_t)0x82U, (uint8_t)0x88U, (uint8_t)0x51U,
    (uint8_t)0x6fU, (uint8_t)0xc9U, (uint8_t)0x26U, (uint8_t)0x45U, (uint8_t)0x9fU, (uint8_t)0x58U,
    (uint8_t)0xe2U, (uint8_t)0xc6U, (uint8_t)0xadU, (uint8_t)0x8dU, (uint8_t)0xf9U, (uint8_t)0xb4U,
    (uint8_t)0x73U, (uint8_t)0xcbU, (uint8_t)0x0fU, (uint8_t)0xc0U, (uint8_t)0x8cU, (uint8_t)0x25U,
    (uint8_t)0x96U, (uint8_t)0xdaU, (uint8_t)0x7cU, (uint8_t)0xf0U, (uint8_t)0xe4U, (uint8_t)0x9bU,
    (uint8_t)0xe4U, (uint8_t)0xb2U, (uint8_t)0x98U, (uint8_t)0xd8U, (uint8_t)0x8cU, (uint8_t)0xeaU,
    (uint8_t)0x92U, (uint8_t)0x7aU, (uint8_t)0xc7U, (uint8_t)0xf5U, (uint8_t)0x39U, (uint8_t)0xf1U,
    (uint8_t)0xedU, (uint8_t)0xf2U, (uint8_t)0x28U, (uint8_t)0x37U, (uint8_t)0x6dU, (uint8_t)0x25U
  };

static uint8_t
test2_expected_sha3_512[64U] =
  {
    (uint8_t)0xb7U, (uint8_t)0x51U, (uint8_t)0x85U, (uint8_t)0x0bU, (uint8_t)0x1aU, (uint8_t)0x57U,
    (uint8_t)0x16U, (uint8_t)0x8aU, (uint8_t)0x56U, (uint8_t)0x93U, (uint8_t)0xcdU, (uint8_t)0x92U,
    (uint8_t)0x4bU, (uint8_t)0x6bU, (uint8_t)0x09U, (uint8_t)0x6eU, (uint8_t)0x08U, (uint8_t)0xf6U,
    (uint8_t)0x21U, (uint8_t)0x82U, (uint8_t)0x74U, (uint8_t)0x44U, (uint8_t)0xf7U, (uint8_t)0x0dU,
    (uint8_t)0x88U, (uint8_t)0x4fU, (uint8_t)0x5dU, (uint8_t)0x02U, (uint8_t)0x40U, (uint8_t)0xd2U,
    (uint8_t)0x71U, (uint8_t)0x2eU, (uint8_t)0x10U, (uint8_t)0xe1U, (uint8_t)0x16U, (uint8_t)0xe9U,
    (uint8_t)0x19U, (uint8_t)0x2aU, (uint8_t)0xf3U, (uint8_t)0xc9U, (uint8_t)0x1aU, (uint8_t)0x7eU,
    (uint8_t)0xc5U, (uint8_t)0x76U, (uint8_t)0x47U, (uint8_t)0xe3U, (uint8_t)0x93U, (uint8_t)0x40U,
    (uint8_t)0x57U, (uint8_t)0x34U, (uint8_t)0x0bU, (uint8_t)0x4cU, (uint8_t)0xf4U, (uint8_t)0x08U,
    (uint8_t)0xd5U, (uint8_t)0xa5U, (uint8_t)0x65U, (uint8_t)0x92U, (uint8_t)0xf8U, (uint8_t)0x27U,
    (uint8_t)0x4eU, (uint8_t)0xecU, (uint8_t)0x53U, (uint8_t)0xf0U
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
test3_expected_sha3_224[28U] =
  {
    (uint8_t)0x8aU, (uint8_t)0x24U, (uint8_t)0x10U, (uint8_t)0x8bU, (uint8_t)0x15U, (uint8_t)0x4aU,
    (uint8_t)0xdaU, (uint8_t)0x21U, (uint8_t)0xc9U, (uint8_t)0xfdU, (uint8_t)0x55U, (uint8_t)0x74U,
    (uint8_t)0x49U, (uint8_t)0x44U, (uint8_t)0x79U, (uint8_t)0xbaU, (uint8_t)0x5cU, (uint8_t)0x7eU,
    (uint8_t)0x7aU, (uint8_t)0xb7U, (uint8_t)0x6eU, (uint8_t)0xf2U, (uint8_t)0x64U, (uint8_t)0xeaU,
    (uint8_t)0xd0U, (uint8_t)0xfcU, (uint8_t)0xceU, (uint8_t)0x33U
  };

static uint8_t
test3_expected_sha3_256[32U] =
  {
    (uint8_t)0x41U, (uint8_t)0xc0U, (uint8_t)0xdbU, (uint8_t)0xa2U, (uint8_t)0xa9U, (uint8_t)0xd6U,
    (uint8_t)0x24U, (uint8_t)0x08U, (uint8_t)0x49U, (uint8_t)0x10U, (uint8_t)0x03U, (uint8_t)0x76U,
    (uint8_t)0xa8U, (uint8_t)0x23U, (uint8_t)0x5eU, (uint8_t)0x2cU, (uint8_t)0x82U, (uint8_t)0xe1U,
    (uint8_t)0xb9U, (uint8_t)0x99U, (uint8_t)0x8aU, (uint8_t)0x99U, (uint8_t)0x9eU, (uint8_t)0x21U,
    (uint8_t)0xdbU, (uint8_t)0x32U, (uint8_t)0xddU, (uint8_t)0x97U, (uint8_t)0x49U, (uint8_t)0x6dU,
    (uint8_t)0x33U, (uint8_t)0x76U
  };

static uint8_t
test3_expected_sha3_384[48U] =
  {
    (uint8_t)0x99U, (uint8_t)0x1cU, (uint8_t)0x66U, (uint8_t)0x57U, (uint8_t)0x55U, (uint8_t)0xebU,
    (uint8_t)0x3aU, (uint8_t)0x4bU, (uint8_t)0x6bU, (uint8_t)0xbdU, (uint8_t)0xfbU, (uint8_t)0x75U,
    (uint8_t)0xc7U, (uint8_t)0x8aU, (uint8_t)0x49U, (uint8_t)0x2eU, (uint8_t)0x8cU, (uint8_t)0x56U,
    (uint8_t)0xa2U, (uint8_t)0x2cU, (uint8_t)0x5cU, (uint8_t)0x4dU, (uint8_t)0x7eU, (uint8_t)0x42U,
    (uint8_t)0x9bU, (uint8_t)0xfdU, (uint8_t)0xbcU, (uint8_t)0x32U, (uint8_t)0xb9U, (uint8_t)0xd4U,
    (uint8_t)0xadU, (uint8_t)0x5aU, (uint8_t)0xa0U, (uint8_t)0x4aU, (uint8_t)0x1fU, (uint8_t)0x07U,
    (uint8_t)0x6eU, (uint8_t)0x62U, (uint8_t)0xfeU, (uint8_t)0xa1U, (uint8_t)0x9eU, (uint8_t)0xefU,
    (uint8_t)0x51U, (uint8_t)0xacU, (uint8_t)0xd0U, (uint8_t)0x65U, (uint8_t)0x7cU, (uint8_t)0x22U
  };

static uint8_t
test3_expected_sha3_512[64U] =
  {
    (uint8_t)0x04U, (uint8_t)0xa3U, (uint8_t)0x71U, (uint8_t)0xe8U, (uint8_t)0x4eU, (uint8_t)0xcfU,
    (uint8_t)0xb5U, (uint8_t)0xb8U, (uint8_t)0xb7U, (uint8_t)0x7cU, (uint8_t)0xb4U, (uint8_t)0x86U,
    (uint8_t)0x10U, (uint8_t)0xfcU, (uint8_t)0xa8U, (uint8_t)0x18U, (uint8_t)0x2dU, (uint8_t)0xd4U,
    (uint8_t)0x57U, (uint8_t)0xceU, (uint8_t)0x6fU, (uint8_t)0x32U, (uint8_t)0x6aU, (uint8_t)0x0fU,
    (uint8_t)0xd3U, (uint8_t)0xd7U, (uint8_t)0xecU, (uint8_t)0x2fU, (uint8_t)0x1eU, (uint8_t)0x91U,
    (uint8_t)0x63U, (uint8_t)0x6dU, (uint8_t)0xeeU, (uint8_t)0x69U, (uint8_t)0x1fU, (uint8_t)0xbeU,
    (uint8_t)0x0cU, (uint8_t)0x98U, (uint8_t)0x53U, (uint8_t)0x02U, (uint8_t)0xbaU, (uint8_t)0x1bU,
    (uint8_t)0x0dU, (uint8_t)0x8dU, (uint8_t)0xc7U, (uint8_t)0x8cU, (uint8_t)0x08U, (uint8_t)0x63U,
    (uint8_t)0x46U, (uint8_t)0xb5U, (uint8_t)0x33U, (uint8_t)0xb4U, (uint8_t)0x9cU, (uint8_t)0x03U,
    (uint8_t)0x0dU, (uint8_t)0x99U, (uint8_t)0xa2U, (uint8_t)0x7dU, (uint8_t)0xafU, (uint8_t)0x11U,
    (uint8_t)0x39U, (uint8_t)0xd6U, (uint8_t)0xe7U, (uint8_t)0x5eU
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
test4_expected_sha3_224[28U] =
  {
    (uint8_t)0x54U, (uint8_t)0x3eU, (uint8_t)0x68U, (uint8_t)0x68U, (uint8_t)0xe1U, (uint8_t)0x66U,
    (uint8_t)0x6cU, (uint8_t)0x1aU, (uint8_t)0x64U, (uint8_t)0x36U, (uint8_t)0x30U, (uint8_t)0xdfU,
    (uint8_t)0x77U, (uint8_t)0x36U, (uint8_t)0x7aU, (uint8_t)0xe5U, (uint8_t)0xa6U, (uint8_t)0x2aU,
    (uint8_t)0x85U, (uint8_t)0x07U, (uint8_t)0x0aU, (uint8_t)0x51U, (uint8_t)0xc1U, (uint8_t)0x4cU,
    (uint8_t)0xbfU, (uint8_t)0x66U, (uint8_t)0x5cU, (uint8_t)0xbcU
  };

static uint8_t
test4_expected_sha3_256[32U] =
  {
    (uint8_t)0x91U, (uint8_t)0x6fU, (uint8_t)0x60U, (uint8_t)0x61U, (uint8_t)0xfeU, (uint8_t)0x87U,
    (uint8_t)0x97U, (uint8_t)0x41U, (uint8_t)0xcaU, (uint8_t)0x64U, (uint8_t)0x69U, (uint8_t)0xb4U,
    (uint8_t)0x39U, (uint8_t)0x71U, (uint8_t)0xdfU, (uint8_t)0xdbU, (uint8_t)0x28U, (uint8_t)0xb1U,
    (uint8_t)0xa3U, (uint8_t)0x2dU, (uint8_t)0xc3U, (uint8_t)0x6cU, (uint8_t)0xb3U, (uint8_t)0x25U,
    (uint8_t)0x4eU, (uint8_t)0x81U, (uint8_t)0x2bU, (uint8_t)0xe2U, (uint8_t)0x7aU, (uint8_t)0xadU,
    (uint8_t)0x1dU, (uint8_t)0x18U
  };

static uint8_t
test4_expected_sha3_384[48U] =
  {
    (uint8_t)0x79U, (uint8_t)0x40U, (uint8_t)0x7dU, (uint8_t)0x3bU, (uint8_t)0x59U, (uint8_t)0x16U,
    (uint8_t)0xb5U, (uint8_t)0x9cU, (uint8_t)0x3eU, (uint8_t)0x30U, (uint8_t)0xb0U, (uint8_t)0x98U,
    (uint8_t)0x22U, (uint8_t)0x97U, (uint8_t)0x47U, (uint8_t)0x91U, (uint8_t)0xc3U, (uint8_t)0x13U,
    (uint8_t)0xfbU, (uint8_t)0x9eU, (uint8_t)0xccU, (uint8_t)0x84U, (uint8_t)0x9eU, (uint8_t)0x40U,
    (uint8_t)0x6fU, (uint8_t)0x23U, (uint8_t)0x59U, (uint8_t)0x2dU, (uint8_t)0x04U, (uint8_t)0xf6U,
    (uint8_t)0x25U, (uint8_t)0xdcU, (uint8_t)0x8cU, (uint8_t)0x70U, (uint8_t)0x9bU, (uint8_t)0x98U,
    (uint8_t)0xb4U, (uint8_t)0x3bU, (uint8_t)0x38U, (uint8_t)0x52U, (uint8_t)0xb3U, (uint8_t)0x37U,
    (uint8_t)0x21U, (uint8_t)0x61U, (uint8_t)0x79U, (uint8_t)0xaaU, (uint8_t)0x7fU, (uint8_t)0xc7U
  };

static uint8_t
test4_expected_sha3_512[64U] =
  {
    (uint8_t)0xafU, (uint8_t)0xebU, (uint8_t)0xb2U, (uint8_t)0xefU, (uint8_t)0x54U, (uint8_t)0x2eU,
    (uint8_t)0x65U, (uint8_t)0x79U, (uint8_t)0xc5U, (uint8_t)0x0cU, (uint8_t)0xadU, (uint8_t)0x06U,
    (uint8_t)0xd2U, (uint8_t)0xe5U, (uint8_t)0x78U, (uint8_t)0xf9U, (uint8_t)0xf8U, (uint8_t)0xddU,
    (uint8_t)0x68U, (uint8_t)0x81U, (uint8_t)0xd7U, (uint8_t)0xdcU, (uint8_t)0x82U, (uint8_t)0x4dU,
    (uint8_t)0x26U, (uint8_t)0x36U, (uint8_t)0x0fU, (uint8_t)0xeeU, (uint8_t)0xbfU, (uint8_t)0x18U,
    (uint8_t)0xa4U, (uint8_t)0xfaU, (uint8_t)0x73U, (uint8_t)0xe3U, (uint8_t)0x26U, (uint8_t)0x11U,
    (uint8_t)0x22U, (uint8_t)0x94U, (uint8_t)0x8eU, (uint8_t)0xfcU, (uint8_t)0xfdU, (uint8_t)0x49U,
    (uint8_t)0x2eU, (uint8_t)0x74U, (uint8_t)0xe8U, (uint8_t)0x2eU, (uint8_t)0x21U, (uint8_t)0x89U,
    (uint8_t)0xedU, (uint8_t)0x0fU, (uint8_t)0xb4U, (uint8_t)0x40U, (uint8_t)0xd1U, (uint8_t)0x87U,
    (uint8_t)0xf3U, (uint8_t)0x82U, (uint8_t)0x27U, (uint8_t)0x0cU, (uint8_t)0xb4U, (uint8_t)0x55U,
    (uint8_t)0xf2U, (uint8_t)0x1dU, (uint8_t)0xd1U, (uint8_t)0x85U
  };

static uint8_t test5_plaintext_shake128[0U] = {  };

static uint8_t
test5_expected_shake128[16U] =
  {
    (uint8_t)0x7fU, (uint8_t)0x9cU, (uint8_t)0x2bU, (uint8_t)0xa4U, (uint8_t)0xe8U, (uint8_t)0x8fU,
    (uint8_t)0x82U, (uint8_t)0x7dU, (uint8_t)0x61U, (uint8_t)0x60U, (uint8_t)0x45U, (uint8_t)0x50U,
    (uint8_t)0x76U, (uint8_t)0x05U, (uint8_t)0x85U, (uint8_t)0x3eU
  };

static uint8_t
test6_plaintext_shake128[14U] =
  {
    (uint8_t)0x52U, (uint8_t)0x97U, (uint8_t)0x7eU, (uint8_t)0x53U, (uint8_t)0x2bU, (uint8_t)0xccU,
    (uint8_t)0xdbU, (uint8_t)0x89U, (uint8_t)0xdfU, (uint8_t)0xefU, (uint8_t)0xf7U, (uint8_t)0xe9U,
    (uint8_t)0xe4U, (uint8_t)0xadU
  };

static uint8_t
test6_expected_shake128[16U] =
  {
    (uint8_t)0xfbU, (uint8_t)0xfbU, (uint8_t)0xa5U, (uint8_t)0xc1U, (uint8_t)0xe1U, (uint8_t)0x79U,
    (uint8_t)0xdfU, (uint8_t)0x14U, (uint8_t)0x69U, (uint8_t)0xfcU, (uint8_t)0xc8U, (uint8_t)0x58U,
    (uint8_t)0x8aU, (uint8_t)0xe5U, (uint8_t)0xd2U, (uint8_t)0xccU
  };

static uint8_t
test7_plaintext_shake128[34U] =
  {
    (uint8_t)0x4aU, (uint8_t)0x20U, (uint8_t)0x6aU, (uint8_t)0x5bU, (uint8_t)0x8aU, (uint8_t)0xa3U,
    (uint8_t)0x58U, (uint8_t)0x6cU, (uint8_t)0x06U, (uint8_t)0x67U, (uint8_t)0xa4U, (uint8_t)0x00U,
    (uint8_t)0x20U, (uint8_t)0xd6U, (uint8_t)0x5fU, (uint8_t)0xf5U, (uint8_t)0x11U, (uint8_t)0xd5U,
    (uint8_t)0x2bU, (uint8_t)0x73U, (uint8_t)0x2eU, (uint8_t)0xf7U, (uint8_t)0xa0U, (uint8_t)0xc5U,
    (uint8_t)0x69U, (uint8_t)0xf1U, (uint8_t)0xeeU, (uint8_t)0x68U, (uint8_t)0x1aU, (uint8_t)0x4fU,
    (uint8_t)0xc3U, (uint8_t)0x62U, (uint8_t)0x00U, (uint8_t)0x65U
  };

static uint8_t
test7_expected_shake128[16U] =
  {
    (uint8_t)0x7bU, (uint8_t)0xb4U, (uint8_t)0x33U, (uint8_t)0x75U, (uint8_t)0x2bU, (uint8_t)0x98U,
    (uint8_t)0xf9U, (uint8_t)0x15U, (uint8_t)0xbeU, (uint8_t)0x51U, (uint8_t)0x82U, (uint8_t)0xbcU,
    (uint8_t)0x1fU, (uint8_t)0x09U, (uint8_t)0x66U, (uint8_t)0x48U
  };

static uint8_t
test8_plaintext_shake128[83U] =
  {
    (uint8_t)0x24U, (uint8_t)0x69U, (uint8_t)0xf1U, (uint8_t)0x01U, (uint8_t)0xc9U, (uint8_t)0xb4U,
    (uint8_t)0x99U, (uint8_t)0xa9U, (uint8_t)0x30U, (uint8_t)0xa9U, (uint8_t)0x7eU, (uint8_t)0xf1U,
    (uint8_t)0xb3U, (uint8_t)0x46U, (uint8_t)0x73U, (uint8_t)0xecU, (uint8_t)0x74U, (uint8_t)0x39U,
    (uint8_t)0x3fU, (uint8_t)0xd9U, (uint8_t)0xfaU, (uint8_t)0xf6U, (uint8_t)0x58U, (uint8_t)0xe3U,
    (uint8_t)0x1fU, (uint8_t)0x06U, (uint8_t)0xeeU, (uint8_t)0x0bU, (uint8_t)0x29U, (uint8_t)0xa2U,
    (uint8_t)0x2bU, (uint8_t)0x62U, (uint8_t)0x37U, (uint8_t)0x80U, (uint8_t)0xbaU, (uint8_t)0x7bU,
    (uint8_t)0xdfU, (uint8_t)0xedU, (uint8_t)0x86U, (uint8_t)0x20U, (uint8_t)0x15U, (uint8_t)0x1cU,
    (uint8_t)0xc4U, (uint8_t)0x44U, (uint8_t)0x4eU, (uint8_t)0xbeU, (uint8_t)0x33U, (uint8_t)0x39U,
    (uint8_t)0xe6U, (uint8_t)0xd2U, (uint8_t)0xa2U, (uint8_t)0x23U, (uint8_t)0xbfU, (uint8_t)0xbfU,
    (uint8_t)0xb4U, (uint8_t)0xadU, (uint8_t)0x2cU, (uint8_t)0xa0U, (uint8_t)0xe0U, (uint8_t)0xfaU,
    (uint8_t)0x0dU, (uint8_t)0xdfU, (uint8_t)0xbbU, (uint8_t)0xdfU, (uint8_t)0x3bU, (uint8_t)0x05U,
    (uint8_t)0x7aU, (uint8_t)0x4fU, (uint8_t)0x26U, (uint8_t)0xd0U, (uint8_t)0xb2U, (uint8_t)0x16U,
    (uint8_t)0xbcU, (uint8_t)0x87U, (uint8_t)0x63U, (uint8_t)0xcaU, (uint8_t)0x8dU, (uint8_t)0x8aU,
    (uint8_t)0x35U, (uint8_t)0xffU, (uint8_t)0x2dU, (uint8_t)0x2dU, (uint8_t)0x01U
  };

static uint8_t
test8_expected_shake128[16U] =
  {
    (uint8_t)0x00U, (uint8_t)0xffU, (uint8_t)0x5eU, (uint8_t)0xf0U, (uint8_t)0xcdU, (uint8_t)0x7fU,
    (uint8_t)0x8fU, (uint8_t)0x90U, (uint8_t)0xadU, (uint8_t)0x94U, (uint8_t)0xb7U, (uint8_t)0x97U,
    (uint8_t)0xe9U, (uint8_t)0xd4U, (uint8_t)0xddU, (uint8_t)0x30U
  };

static uint8_t test9_plaintext_shake256[0U] = {  };

static uint8_t
test9_expected_shake256[32U] =
  {
    (uint8_t)0x46U, (uint8_t)0xb9U, (uint8_t)0xddU, (uint8_t)0x2bU, (uint8_t)0x0bU, (uint8_t)0xa8U,
    (uint8_t)0x8dU, (uint8_t)0x13U, (uint8_t)0x23U, (uint8_t)0x3bU, (uint8_t)0x3fU, (uint8_t)0xebU,
    (uint8_t)0x74U, (uint8_t)0x3eU, (uint8_t)0xebU, (uint8_t)0x24U, (uint8_t)0x3fU, (uint8_t)0xcdU,
    (uint8_t)0x52U, (uint8_t)0xeaU, (uint8_t)0x62U, (uint8_t)0xb8U, (uint8_t)0x1bU, (uint8_t)0x82U,
    (uint8_t)0xb5U, (uint8_t)0x0cU, (uint8_t)0x27U, (uint8_t)0x64U, (uint8_t)0x6eU, (uint8_t)0xd5U,
    (uint8_t)0x76U, (uint8_t)0x2fU
  };

static uint8_t
test10_plaintext_shake256[17U] =
  {
    (uint8_t)0xf9U, (uint8_t)0xdaU, (uint8_t)0x78U, (uint8_t)0xc8U, (uint8_t)0x90U, (uint8_t)0x84U,
    (uint8_t)0x70U, (uint8_t)0x40U, (uint8_t)0x45U, (uint8_t)0x4bU, (uint8_t)0xa6U, (uint8_t)0x42U,
    (uint8_t)0x98U, (uint8_t)0x82U, (uint8_t)0xb0U, (uint8_t)0x54U, (uint8_t)0x09U
  };

static uint8_t
test10_expected_shake256[32U] =
  {
    (uint8_t)0xa8U, (uint8_t)0x49U, (uint8_t)0x83U, (uint8_t)0xc9U, (uint8_t)0xfeU, (uint8_t)0x75U,
    (uint8_t)0xadU, (uint8_t)0x0dU, (uint8_t)0xe1U, (uint8_t)0x9eU, (uint8_t)0x2cU, (uint8_t)0x84U,
    (uint8_t)0x20U, (uint8_t)0xa7U, (uint8_t)0xeaU, (uint8_t)0x85U, (uint8_t)0xb2U, (uint8_t)0x51U,
    (uint8_t)0x02U, (uint8_t)0x19U, (uint8_t)0x56U, (uint8_t)0x14U, (uint8_t)0xdfU, (uint8_t)0xa5U,
    (uint8_t)0x34U, (uint8_t)0x7dU, (uint8_t)0xe6U, (uint8_t)0x0aU, (uint8_t)0x1cU, (uint8_t)0xe1U,
    (uint8_t)0x3bU, (uint8_t)0x60U
  };

static uint8_t
test11_plaintext_shake256[32U] =
  {
    (uint8_t)0xefU, (uint8_t)0x89U, (uint8_t)0x6cU, (uint8_t)0xdcU, (uint8_t)0xb3U, (uint8_t)0x63U,
    (uint8_t)0xa6U, (uint8_t)0x15U, (uint8_t)0x91U, (uint8_t)0x78U, (uint8_t)0xa1U, (uint8_t)0xbbU,
    (uint8_t)0x1cU, (uint8_t)0x99U, (uint8_t)0x39U, (uint8_t)0x46U, (uint8_t)0xc5U, (uint8_t)0x04U,
    (uint8_t)0x02U, (uint8_t)0x09U, (uint8_t)0x5cU, (uint8_t)0xdaU, (uint8_t)0xeaU, (uint8_t)0x4fU,
    (uint8_t)0xd4U, (uint8_t)0xd4U, (uint8_t)0x19U, (uint8_t)0xaaU, (uint8_t)0x47U, (uint8_t)0x32U,
    (uint8_t)0x1cU, (uint8_t)0x88U
  };

static uint8_t
test11_expected_shake256[32U] =
  {
    (uint8_t)0x7aU, (uint8_t)0xbbU, (uint8_t)0xa4U, (uint8_t)0xe8U, (uint8_t)0xb8U, (uint8_t)0xddU,
    (uint8_t)0x76U, (uint8_t)0x6bU, (uint8_t)0xbaU, (uint8_t)0xbeU, (uint8_t)0x98U, (uint8_t)0xf8U,
    (uint8_t)0xf1U, (uint8_t)0x69U, (uint8_t)0xcbU, (uint8_t)0x62U, (uint8_t)0x08U, (uint8_t)0x67U,
    (uint8_t)0x4dU, (uint8_t)0xe1U, (uint8_t)0x9aU, (uint8_t)0x51U, (uint8_t)0xd7U, (uint8_t)0x3cU,
    (uint8_t)0x92U, (uint8_t)0xb7U, (uint8_t)0xdcU, (uint8_t)0x04U, (uint8_t)0xa4U, (uint8_t)0xb5U,
    (uint8_t)0xeeU, (uint8_t)0x3dU
  };

static uint8_t
test12_plaintext_shake256[78U] =
  {
    (uint8_t)0xdeU, (uint8_t)0x70U, (uint8_t)0x1fU, (uint8_t)0x10U, (uint8_t)0xadU, (uint8_t)0x39U,
    (uint8_t)0x61U, (uint8_t)0xb0U, (uint8_t)0xdaU, (uint8_t)0xccU, (uint8_t)0x96U, (uint8_t)0x87U,
    (uint8_t)0x3aU, (uint8_t)0x3cU, (uint8_t)0xd5U, (uint8_t)0x58U, (uint8_t)0x55U, (uint8_t)0x81U,
    (uint8_t)0x88U, (uint8_t)0xffU, (uint8_t)0x69U, (uint8_t)0x6dU, (uint8_t)0x85U, (uint8_t)0x01U,
    (uint8_t)0xb2U, (uint8_t)0xe2U, (uint8_t)0x7bU, (uint8_t)0x67U, (uint8_t)0xe9U, (uint8_t)0x41U,
    (uint8_t)0x90U, (uint8_t)0xcdU, (uint8_t)0x0bU, (uint8_t)0x25U, (uint8_t)0x48U, (uint8_t)0xb6U,
    (uint8_t)0x5bU, (uint8_t)0x52U, (uint8_t)0xa9U, (uint8_t)0x22U, (uint8_t)0xaaU, (uint8_t)0xe8U,
    (uint8_t)0x9dU, (uint8_t)0x63U, (uint8_t)0xd6U, (uint8_t)0xddU, (uint8_t)0x97U, (uint8_t)0x2cU,
    (uint8_t)0x91U, (uint8_t)0xa9U, (uint8_t)0x79U, (uint8_t)0xebU, (uint8_t)0x63U, (uint8_t)0x43U,
    (uint8_t)0xb6U, (uint8_t)0x58U, (uint8_t)0xf2U, (uint8_t)0x4dU, (uint8_t)0xb3U, (uint8_t)0x4eU,
    (uint8_t)0x82U, (uint8_t)0x8bU, (uint8_t)0x74U, (uint8_t)0xdbU, (uint8_t)0xb8U, (uint8_t)0x9aU,
    (uint8_t)0x74U, (uint8_t)0x93U, (uint8_t)0xa3U, (uint8_t)0xdfU, (uint8_t)0xd4U, (uint8_t)0x29U,
    (uint8_t)0xfdU, (uint8_t)0xbdU, (uint8_t)0xb8U, (uint8_t)0x40U, (uint8_t)0xadU, (uint8_t)0x0bU
  };

static uint8_t
test12_expected_shake256[32U] =
  {
    (uint8_t)0x64U, (uint8_t)0x2fU, (uint8_t)0x3fU, (uint8_t)0x23U, (uint8_t)0x5aU, (uint8_t)0xc7U,
    (uint8_t)0xe3U, (uint8_t)0xd4U, (uint8_t)0x34U, (uint8_t)0x06U, (uint8_t)0x3bU, (uint8_t)0x5fU,
    (uint8_t)0xc9U, (uint8_t)0x21U, (uint8_t)0x5fU, (uint8_t)0xc3U, (uint8_t)0xf0U, (uint8_t)0xe5U,
    (uint8_t)0x91U, (uint8_t)0xe2U, (uint8_t)0xe7U, (uint8_t)0xfdU, (uint8_t)0x17U, (uint8_t)0x66U,
    (uint8_t)0x8dU, (uint8_t)0x1aU, (uint8_t)0x0cU, (uint8_t)0x87U, (uint8_t)0x46U, (uint8_t)0x87U,
    (uint8_t)0x35U, (uint8_t)0xc2U
  };

exit_code main()
{
  C_String_print("\nTEST 1. SHA3\n");
  test_sha3((uint32_t)0U,
    test1_plaintext,
    test1_expected_sha3_224,
    test1_expected_sha3_256,
    test1_expected_sha3_384,
    test1_expected_sha3_512);
  C_String_print("\nTEST 2. SHA3\n");
  test_sha3((uint32_t)3U,
    test2_plaintext,
    test2_expected_sha3_224,
    test2_expected_sha3_256,
    test2_expected_sha3_384,
    test2_expected_sha3_512);
  C_String_print("\nTEST 3. SHA3\n");
  test_sha3((uint32_t)56U,
    test3_plaintext,
    test3_expected_sha3_224,
    test3_expected_sha3_256,
    test3_expected_sha3_384,
    test3_expected_sha3_512);
  C_String_print("\nTEST 4. SHA3\n");
  test_sha3((uint32_t)112U,
    test4_plaintext,
    test4_expected_sha3_224,
    test4_expected_sha3_256,
    test4_expected_sha3_384,
    test4_expected_sha3_512);
  C_String_print("\nTEST 5. SHAKE128\n");
  test_shake128((uint32_t)0U, test5_plaintext_shake128, (uint32_t)16U, test5_expected_shake128);
  C_String_print("\nTEST 6. SHAKE128\n");
  test_shake128((uint32_t)14U, test6_plaintext_shake128, (uint32_t)16U, test6_expected_shake128);
  C_String_print("\nTEST 7. SHAKE128\n");
  test_shake128((uint32_t)34U, test7_plaintext_shake128, (uint32_t)16U, test7_expected_shake128);
  C_String_print("\nTEST 8. SHAKE128\n");
  test_shake128((uint32_t)83U, test8_plaintext_shake128, (uint32_t)16U, test8_expected_shake128);
  C_String_print("\nTEST 9. SHAKE256\n");
  test_shake256((uint32_t)0U, test9_plaintext_shake256, (uint32_t)32U, test9_expected_shake256);
  C_String_print("\nTEST 10. SHAKE256\n");
  test_shake256((uint32_t)17U,
    test10_plaintext_shake256,
    (uint32_t)32U,
    test10_expected_shake256);
  C_String_print("\nTEST 11. SHAKE256\n");
  test_shake256((uint32_t)32U,
    test11_plaintext_shake256,
    (uint32_t)32U,
    test11_expected_shake256);
  C_String_print("\nTEST 12. SHAKE256\n");
  test_shake256((uint32_t)78U,
    test12_plaintext_shake256,
    (uint32_t)32U,
    test12_expected_shake256);
  return EXIT_SUCCESS;
}

