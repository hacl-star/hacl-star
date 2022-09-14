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


#include "Hacl_Test_K256.h"

#include "internal/Hacl_Lib.h"
#include "internal/Hacl_Krmllib.h"

const
uint8_t
pk1[64U] =
  {
    (uint8_t)0xb8U, (uint8_t)0x38U, (uint8_t)0xffU, (uint8_t)0x44U, (uint8_t)0xe5U, (uint8_t)0xbcU,
    (uint8_t)0x17U, (uint8_t)0x7bU, (uint8_t)0xf2U, (uint8_t)0x11U, (uint8_t)0x89U, (uint8_t)0xd0U,
    (uint8_t)0x76U, (uint8_t)0x60U, (uint8_t)0x82U, (uint8_t)0xfcU, (uint8_t)0x9dU, (uint8_t)0x84U,
    (uint8_t)0x32U, (uint8_t)0x26U, (uint8_t)0x88U, (uint8_t)0x7fU, (uint8_t)0xc9U, (uint8_t)0x76U,
    (uint8_t)0x03U, (uint8_t)0x71U, (uint8_t)0x10U, (uint8_t)0x0bU, (uint8_t)0x7eU, (uint8_t)0xe2U,
    (uint8_t)0x0aU, (uint8_t)0x6fU, (uint8_t)0xf0U, (uint8_t)0xc9U, (uint8_t)0xd7U, (uint8_t)0x5bU,
    (uint8_t)0xfbU, (uint8_t)0xa7U, (uint8_t)0xb3U, (uint8_t)0x1aU, (uint8_t)0x6bU, (uint8_t)0xcaU,
    (uint8_t)0x19U, (uint8_t)0x74U, (uint8_t)0x49U, (uint8_t)0x6eU, (uint8_t)0xebU, (uint8_t)0x56U,
    (uint8_t)0xdeU, (uint8_t)0x35U, (uint8_t)0x70U, (uint8_t)0x71U, (uint8_t)0x95U, (uint8_t)0x5dU,
    (uint8_t)0x83U, (uint8_t)0xc4U, (uint8_t)0xb1U, (uint8_t)0xbaU, (uint8_t)0xdaU, (uint8_t)0xa0U,
    (uint8_t)0xb2U, (uint8_t)0x18U, (uint8_t)0x32U, (uint8_t)0xe9U
  };

const
uint8_t
msg1[6U] =
  {
    (uint8_t)0x31U, (uint8_t)0x32U, (uint8_t)0x33U, (uint8_t)0x34U, (uint8_t)0x30U, (uint8_t)0x30U
  };

const
uint8_t
sgnt1[64U] =
  {
    (uint8_t)0x81U, (uint8_t)0x3eU, (uint8_t)0xf7U, (uint8_t)0x9cU, (uint8_t)0xceU, (uint8_t)0xfaU,
    (uint8_t)0x9aU, (uint8_t)0x56U, (uint8_t)0xf7U, (uint8_t)0xbaU, (uint8_t)0x80U, (uint8_t)0x5fU,
    (uint8_t)0x0eU, (uint8_t)0x47U, (uint8_t)0x85U, (uint8_t)0x84U, (uint8_t)0xfeU, (uint8_t)0x5fU,
    (uint8_t)0x0dU, (uint8_t)0xd5U, (uint8_t)0xf5U, (uint8_t)0x67U, (uint8_t)0xbcU, (uint8_t)0x09U,
    (uint8_t)0xb5U, (uint8_t)0x12U, (uint8_t)0x3cU, (uint8_t)0xcbU, (uint8_t)0xc9U, (uint8_t)0x83U,
    (uint8_t)0x23U, (uint8_t)0x65U, (uint8_t)0x6fU, (uint8_t)0xf1U, (uint8_t)0x8aU, (uint8_t)0x52U,
    (uint8_t)0xdcU, (uint8_t)0xc0U, (uint8_t)0x33U, (uint8_t)0x6fU, (uint8_t)0x7aU, (uint8_t)0xf6U,
    (uint8_t)0x24U, (uint8_t)0x00U, (uint8_t)0xa6U, (uint8_t)0xddU, (uint8_t)0x9bU, (uint8_t)0x81U,
    (uint8_t)0x07U, (uint8_t)0x32U, (uint8_t)0xbaU, (uint8_t)0xf1U, (uint8_t)0xffU, (uint8_t)0x75U,
    (uint8_t)0x80U, (uint8_t)0x00U, (uint8_t)0xd6U, (uint8_t)0xf6U, (uint8_t)0x13U, (uint8_t)0xa5U,
    (uint8_t)0x56U, (uint8_t)0xebU, (uint8_t)0x31U, (uint8_t)0xbaU
  };

const
uint8_t
sk2[32U] =
  {
    (uint8_t)0xebU, (uint8_t)0xb2U, (uint8_t)0xc0U, (uint8_t)0x82U, (uint8_t)0xfdU, (uint8_t)0x77U,
    (uint8_t)0x27U, (uint8_t)0x89U, (uint8_t)0x0aU, (uint8_t)0x28U, (uint8_t)0xacU, (uint8_t)0x82U,
    (uint8_t)0xf6U, (uint8_t)0xbdU, (uint8_t)0xf9U, (uint8_t)0x7bU, (uint8_t)0xadU, (uint8_t)0x8dU,
    (uint8_t)0xe9U, (uint8_t)0xf5U, (uint8_t)0xd7U, (uint8_t)0xc9U, (uint8_t)0x02U, (uint8_t)0x86U,
    (uint8_t)0x92U, (uint8_t)0xdeU, (uint8_t)0x1aU, (uint8_t)0x25U, (uint8_t)0x5cU, (uint8_t)0xadU,
    (uint8_t)0x3eU, (uint8_t)0x0fU
  };

const
uint8_t
pk2[64U] =
  {
    (uint8_t)0x77U, (uint8_t)0x9dU, (uint8_t)0xd1U, (uint8_t)0x97U, (uint8_t)0xa5U, (uint8_t)0xdfU,
    (uint8_t)0x97U, (uint8_t)0x7eU, (uint8_t)0xd2U, (uint8_t)0xcfU, (uint8_t)0x6cU, (uint8_t)0xb3U,
    (uint8_t)0x1dU, (uint8_t)0x82U, (uint8_t)0xd4U, (uint8_t)0x33U, (uint8_t)0x28U, (uint8_t)0xb7U,
    (uint8_t)0x90U, (uint8_t)0xdcU, (uint8_t)0x6bU, (uint8_t)0x3bU, (uint8_t)0x7dU, (uint8_t)0x44U,
    (uint8_t)0x37U, (uint8_t)0xa4U, (uint8_t)0x27U, (uint8_t)0xbdU, (uint8_t)0x58U, (uint8_t)0x47U,
    (uint8_t)0xdfU, (uint8_t)0xcdU, (uint8_t)0xe9U, (uint8_t)0x4bU, (uint8_t)0x72U, (uint8_t)0x4aU,
    (uint8_t)0x55U, (uint8_t)0x5bU, (uint8_t)0x6dU, (uint8_t)0x01U, (uint8_t)0x7bU, (uint8_t)0xb7U,
    (uint8_t)0x60U, (uint8_t)0x7cU, (uint8_t)0x3eU, (uint8_t)0x32U, (uint8_t)0x81U, (uint8_t)0xdaU,
    (uint8_t)0xf5U, (uint8_t)0xb1U, (uint8_t)0x69U, (uint8_t)0x9dU, (uint8_t)0x6eU, (uint8_t)0xf4U,
    (uint8_t)0x12U, (uint8_t)0x49U, (uint8_t)0x75U, (uint8_t)0xc9U, (uint8_t)0x23U, (uint8_t)0x7bU,
    (uint8_t)0x91U, (uint8_t)0x7dU, (uint8_t)0x42U, (uint8_t)0x6fU
  };

const
uint8_t
nonce2[32U] =
  {
    (uint8_t)0x49U, (uint8_t)0xa0U, (uint8_t)0xd7U, (uint8_t)0xb7U, (uint8_t)0x86U, (uint8_t)0xecU,
    (uint8_t)0x9cU, (uint8_t)0xdeU, (uint8_t)0x0dU, (uint8_t)0x07U, (uint8_t)0x21U, (uint8_t)0xd7U,
    (uint8_t)0x28U, (uint8_t)0x04U, (uint8_t)0xbeU, (uint8_t)0xfdU, (uint8_t)0x06U, (uint8_t)0x57U,
    (uint8_t)0x1cU, (uint8_t)0x97U, (uint8_t)0x4bU, (uint8_t)0x19U, (uint8_t)0x1eU, (uint8_t)0xfbU,
    (uint8_t)0x42U, (uint8_t)0xecU, (uint8_t)0xf3U, (uint8_t)0x22U, (uint8_t)0xbaU, (uint8_t)0x9dU,
    (uint8_t)0xddU, (uint8_t)0x9aU
  };

const
uint8_t
msgHash2[32U] =
  {
    (uint8_t)0x4bU, (uint8_t)0x68U, (uint8_t)0x8dU, (uint8_t)0xf4U, (uint8_t)0x0bU, (uint8_t)0xceU,
    (uint8_t)0xdbU, (uint8_t)0xe6U, (uint8_t)0x41U, (uint8_t)0xddU, (uint8_t)0xb1U, (uint8_t)0x6fU,
    (uint8_t)0xf0U, (uint8_t)0xa1U, (uint8_t)0x84U, (uint8_t)0x2dU, (uint8_t)0x9cU, (uint8_t)0x67U,
    (uint8_t)0xeaU, (uint8_t)0x1cU, (uint8_t)0x3bU, (uint8_t)0xf6U, (uint8_t)0x3fU, (uint8_t)0x3eU,
    (uint8_t)0x04U, (uint8_t)0x71U, (uint8_t)0xbaU, (uint8_t)0xa6U, (uint8_t)0x64U, (uint8_t)0x53U,
    (uint8_t)0x1dU, (uint8_t)0x1aU
  };

const
uint8_t
sgnt2[64U] =
  {
    (uint8_t)0x24U, (uint8_t)0x10U, (uint8_t)0x97U, (uint8_t)0xefU, (uint8_t)0xbfU, (uint8_t)0x8bU,
    (uint8_t)0x63U, (uint8_t)0xbfU, (uint8_t)0x14U, (uint8_t)0x5cU, (uint8_t)0x89U, (uint8_t)0x61U,
    (uint8_t)0xdbU, (uint8_t)0xdfU, (uint8_t)0x10U, (uint8_t)0xc3U, (uint8_t)0x10U, (uint8_t)0xefU,
    (uint8_t)0xbbU, (uint8_t)0x3bU, (uint8_t)0x26U, (uint8_t)0x76U, (uint8_t)0xbbU, (uint8_t)0xc0U,
    (uint8_t)0xf8U, (uint8_t)0xb0U, (uint8_t)0x85U, (uint8_t)0x05U, (uint8_t)0xc9U, (uint8_t)0xe2U,
    (uint8_t)0xf7U, (uint8_t)0x95U, (uint8_t)0x02U, (uint8_t)0x10U, (uint8_t)0x06U, (uint8_t)0xb7U,
    (uint8_t)0x83U, (uint8_t)0x86U, (uint8_t)0x09U, (uint8_t)0x33U, (uint8_t)0x9eU, (uint8_t)0x8bU,
    (uint8_t)0x41U, (uint8_t)0x5aU, (uint8_t)0x7fU, (uint8_t)0x9aU, (uint8_t)0xcbU, (uint8_t)0x1bU,
    (uint8_t)0x66U, (uint8_t)0x18U, (uint8_t)0x28U, (uint8_t)0x13U, (uint8_t)0x1aU, (uint8_t)0xefU,
    (uint8_t)0x1eU, (uint8_t)0xcbU, (uint8_t)0xc7U, (uint8_t)0x95U, (uint8_t)0x5dU, (uint8_t)0xfbU,
    (uint8_t)0x01U, (uint8_t)0xf3U, (uint8_t)0xcaU, (uint8_t)0x0eU
  };

static uint8_t *const_to_buffer__uint8_t(const uint8_t *b)
{
  return (uint8_t *)b;
}

void test_verify()
{
  bool
  b =
    Hacl_K256_ECDSA_ecdsa_verify_sha256((uint32_t)6U,
      const_to_buffer__uint8_t(msg1),
      const_to_buffer__uint8_t(pk1),
      const_to_buffer__uint8_t(sgnt1));
  if (b)
  {
    C_String_print("Test K256 ecdsa verification: Success!\n");
    return;
  }
  C_String_print("Test K256 ecdsa verification: Failure :(\n");
}

static const uint8_t *to_const__uint8_t(Lib_Buffer_buftype t, void *b)
{
  switch (t)
  {
    case Lib_Buffer_MUT:
      {
        return (const uint8_t *)(void *)(uint8_t *)b;
      }
    case Lib_Buffer_IMMUT:
      {
        return (const uint8_t *)(void *)(uint8_t *)b;
      }
    case Lib_Buffer_CONST:
      {
        return (const uint8_t *)(void *)b;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

void test_sign_and_verify()
{
  uint8_t sgnt[64U] = { 0U };
  bool
  uu____0 =
    Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(sgnt,
      const_to_buffer__uint8_t(msgHash2),
      const_to_buffer__uint8_t(sk2),
      const_to_buffer__uint8_t(nonce2));
  Lib_PrintBuffer_print_compare_display((uint32_t)64U,
    to_const__uint8_t(Lib_Buffer_MUT, (void *)sgnt),
    sgnt2);
  bool
  b =
    Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(const_to_buffer__uint8_t(msgHash2),
      const_to_buffer__uint8_t(pk2),
      const_to_buffer__uint8_t(sgnt2));
  if (b)
  {
    C_String_print("Test K256 ecdsa verification: Success!\n");
  }
  else
  {
    C_String_print("Test K256 ecdsa verification: Failure :(\n");
  }
}

void test_public_key_compressed()
{
  uint8_t pk_c[33U] = { 0U };
  uint8_t pk_raw_c[64U] = { 0U };
  Hacl_K256_ECDSA_public_key_compressed_from_raw(pk_c, const_to_buffer__uint8_t(pk1));
  bool b = Hacl_K256_ECDSA_public_key_compressed_to_raw(pk_raw_c, pk_c);
  if (b)
  {
    C_String_print("Test K256 pk_compressed (Some): \n");
    Lib_PrintBuffer_print_compare_display((uint32_t)64U,
      pk1,
      to_const__uint8_t(Lib_Buffer_MUT, (void *)pk_raw_c));
  }
  else
  {
    C_String_print("Test K256 pk_compressed (None): Failure :(\n");
  }
}

void test_public_key_uncompressed()
{
  uint8_t pk_u[65U] = { 0U };
  uint8_t pk_raw_u[64U] = { 0U };
  Hacl_K256_ECDSA_public_key_uncompressed_from_raw(pk_u, const_to_buffer__uint8_t(pk1));
  bool b = Hacl_K256_ECDSA_public_key_uncompressed_to_raw(pk_raw_u, pk_u);
  if (b)
  {
    C_String_print("Test K256 pk_uncompressed (Some): \n");
    Lib_PrintBuffer_print_compare_display((uint32_t)64U,
      pk1,
      to_const__uint8_t(Lib_Buffer_MUT, (void *)pk_raw_u));
  }
  else
  {
    C_String_print("Test K256 pk_uncompressed (None): Failure :(\n");
  }
}

exit_code main()
{
  C_String_print("\nTEST 1. K256\n");
  test_verify();
  C_String_print("\nTEST 2. K256\n");
  test_sign_and_verify();
  C_String_print("\nTEST 3. K256\n");
  test_public_key_compressed();
  C_String_print("\nTEST 4. K256\n");
  test_public_key_uncompressed();
  return EXIT_SUCCESS;
}

