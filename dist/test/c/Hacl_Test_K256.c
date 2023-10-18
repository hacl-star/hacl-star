/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
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

extern void C_String_print(Prims_string uu___);

extern bool
Lib_PrintBuffer_result_compare_display(uint32_t len, const uint8_t *buf0, const uint8_t *buf1);

/*******************************************************************************
  Verified C library for ECDSA signing and verification on the secp256k1 curve.

  For the comments on low-S normalization (or canonical lowest S value), see:
    • https://en.bitcoin.it/wiki/BIP_0062
    • https://yondon.blog/2019/01/01/how-not-to-use-ecdsa/
    • https://eklitzke.org/bitcoin-transaction-malleability

  For example, bitcoin-core/secp256k1 *always* performs low-S normalization.

*******************************************************************************/


/**
Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `msgHash`, `private_key`, and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function DOESN'T perform low-S normalization, see `secp256k1_ecdsa_sign_hashed_msg` if needed.

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
*/
extern bool
Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(
  uint8_t *signature,
  uint8_t *msgHash,
  uint8_t *private_key,
  uint8_t *nonce
);

/**
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msgHash` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function ACCEPTS non low-S normalized signatures, see `secp256k1_ecdsa_verify_hashed_msg` if needed.

  The function also checks whether `public key` is valid.
*/
extern bool
Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(uint8_t *m, uint8_t *public_key, uint8_t *signature);

/**
Verify an ECDSA signature using SHA2-256.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function first hashes a message `msg` with SHA2-256 and then calls `ecdsa_verify_hashed_msg`.

  The function ACCEPTS non low-S normalized signatures, see `secp256k1_ecdsa_verify_sha256` if needed.
*/
extern bool
Hacl_K256_ECDSA_ecdsa_verify_sha256(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature
);

/*******************************************************************************
  Parsing and Serializing public keys.

  A public key is a point (x, y) on the secp256k1 curve.

  The point can be represented in the following three ways.
    • raw          = [ x || y ], 64 bytes
    • uncompressed = [ 0x04 || x || y ], 65 bytes
    • compressed   = [ (0x02 for even `y` and 0x03 for odd `y`) || x ], 33 bytes

*******************************************************************************/


/**
Convert a public key from uncompressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].

  The function DOESN'T check whether (x, y) is valid point.
*/
extern bool Hacl_K256_ECDSA_public_key_uncompressed_to_raw(uint8_t *pk_raw, uint8_t *pk);

/**
Convert a public key from raw to its uncompressed form.

  The outparam `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is valid point.
*/
extern void Hacl_K256_ECDSA_public_key_uncompressed_from_raw(uint8_t *pk, uint8_t *pk_raw);

/**
Convert a public key from compressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].

  The function also checks whether (x, y) is valid point.
*/
extern bool Hacl_K256_ECDSA_public_key_compressed_to_raw(uint8_t *pk_raw, uint8_t *pk);

/**
Convert a public key from raw to its compressed form.

  The outparam `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is valid point.
*/
extern void Hacl_K256_ECDSA_public_key_compressed_from_raw(uint8_t *pk, uint8_t *pk_raw);


/******************/
/* ECDH agreement */
/******************/

/**
Compute the public key from the private key.

  The function returns `true` if a private key is valid and `false` otherwise.

  The outparam `public_key`  points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The private key is valid:
    • 0 < `private_key` < the order of the curve.
*/
extern bool Hacl_K256_ECDSA_secret_to_public(uint8_t *public_key, uint8_t *private_key);

static uint8_t
pk1[64U] =
  {
    0xb8U, 0x38U, 0xffU, 0x44U, 0xe5U, 0xbcU, 0x17U, 0x7bU, 0xf2U, 0x11U, 0x89U, 0xd0U, 0x76U,
    0x60U, 0x82U, 0xfcU, 0x9dU, 0x84U, 0x32U, 0x26U, 0x88U, 0x7fU, 0xc9U, 0x76U, 0x03U, 0x71U,
    0x10U, 0x0bU, 0x7eU, 0xe2U, 0x0aU, 0x6fU, 0xf0U, 0xc9U, 0xd7U, 0x5bU, 0xfbU, 0xa7U, 0xb3U,
    0x1aU, 0x6bU, 0xcaU, 0x19U, 0x74U, 0x49U, 0x6eU, 0xebU, 0x56U, 0xdeU, 0x35U, 0x70U, 0x71U,
    0x95U, 0x5dU, 0x83U, 0xc4U, 0xb1U, 0xbaU, 0xdaU, 0xa0U, 0xb2U, 0x18U, 0x32U, 0xe9U
  };

static uint8_t msg1[6U] = { 0x31U, 0x32U, 0x33U, 0x34U, 0x30U, 0x30U };

static uint8_t
sgnt1[64U] =
  {
    0x81U, 0x3eU, 0xf7U, 0x9cU, 0xceU, 0xfaU, 0x9aU, 0x56U, 0xf7U, 0xbaU, 0x80U, 0x5fU, 0x0eU,
    0x47U, 0x85U, 0x84U, 0xfeU, 0x5fU, 0x0dU, 0xd5U, 0xf5U, 0x67U, 0xbcU, 0x09U, 0xb5U, 0x12U,
    0x3cU, 0xcbU, 0xc9U, 0x83U, 0x23U, 0x65U, 0x6fU, 0xf1U, 0x8aU, 0x52U, 0xdcU, 0xc0U, 0x33U,
    0x6fU, 0x7aU, 0xf6U, 0x24U, 0x00U, 0xa6U, 0xddU, 0x9bU, 0x81U, 0x07U, 0x32U, 0xbaU, 0xf1U,
    0xffU, 0x75U, 0x80U, 0x00U, 0xd6U, 0xf6U, 0x13U, 0xa5U, 0x56U, 0xebU, 0x31U, 0xbaU
  };

static uint8_t
sk2[32U] =
  {
    0xebU, 0xb2U, 0xc0U, 0x82U, 0xfdU, 0x77U, 0x27U, 0x89U, 0x0aU, 0x28U, 0xacU, 0x82U, 0xf6U,
    0xbdU, 0xf9U, 0x7bU, 0xadU, 0x8dU, 0xe9U, 0xf5U, 0xd7U, 0xc9U, 0x02U, 0x86U, 0x92U, 0xdeU,
    0x1aU, 0x25U, 0x5cU, 0xadU, 0x3eU, 0x0fU
  };

static uint8_t
pk2[64U] =
  {
    0x77U, 0x9dU, 0xd1U, 0x97U, 0xa5U, 0xdfU, 0x97U, 0x7eU, 0xd2U, 0xcfU, 0x6cU, 0xb3U, 0x1dU,
    0x82U, 0xd4U, 0x33U, 0x28U, 0xb7U, 0x90U, 0xdcU, 0x6bU, 0x3bU, 0x7dU, 0x44U, 0x37U, 0xa4U,
    0x27U, 0xbdU, 0x58U, 0x47U, 0xdfU, 0xcdU, 0xe9U, 0x4bU, 0x72U, 0x4aU, 0x55U, 0x5bU, 0x6dU,
    0x01U, 0x7bU, 0xb7U, 0x60U, 0x7cU, 0x3eU, 0x32U, 0x81U, 0xdaU, 0xf5U, 0xb1U, 0x69U, 0x9dU,
    0x6eU, 0xf4U, 0x12U, 0x49U, 0x75U, 0xc9U, 0x23U, 0x7bU, 0x91U, 0x7dU, 0x42U, 0x6fU
  };

static uint8_t
nonce2[32U] =
  {
    0x49U, 0xa0U, 0xd7U, 0xb7U, 0x86U, 0xecU, 0x9cU, 0xdeU, 0x0dU, 0x07U, 0x21U, 0xd7U, 0x28U,
    0x04U, 0xbeU, 0xfdU, 0x06U, 0x57U, 0x1cU, 0x97U, 0x4bU, 0x19U, 0x1eU, 0xfbU, 0x42U, 0xecU,
    0xf3U, 0x22U, 0xbaU, 0x9dU, 0xddU, 0x9aU
  };

static uint8_t
msgHash2[32U] =
  {
    0x4bU, 0x68U, 0x8dU, 0xf4U, 0x0bU, 0xceU, 0xdbU, 0xe6U, 0x41U, 0xddU, 0xb1U, 0x6fU, 0xf0U,
    0xa1U, 0x84U, 0x2dU, 0x9cU, 0x67U, 0xeaU, 0x1cU, 0x3bU, 0xf6U, 0x3fU, 0x3eU, 0x04U, 0x71U,
    0xbaU, 0xa6U, 0x64U, 0x53U, 0x1dU, 0x1aU
  };

static uint8_t
sgnt2[64U] =
  {
    0x24U, 0x10U, 0x97U, 0xefU, 0xbfU, 0x8bU, 0x63U, 0xbfU, 0x14U, 0x5cU, 0x89U, 0x61U, 0xdbU,
    0xdfU, 0x10U, 0xc3U, 0x10U, 0xefU, 0xbbU, 0x3bU, 0x26U, 0x76U, 0xbbU, 0xc0U, 0xf8U, 0xb0U,
    0x85U, 0x05U, 0xc9U, 0xe2U, 0xf7U, 0x95U, 0x02U, 0x10U, 0x06U, 0xb7U, 0x83U, 0x86U, 0x09U,
    0x33U, 0x9eU, 0x8bU, 0x41U, 0x5aU, 0x7fU, 0x9aU, 0xcbU, 0x1bU, 0x66U, 0x18U, 0x28U, 0x13U,
    0x1aU, 0xefU, 0x1eU, 0xcbU, 0xc7U, 0x95U, 0x5dU, 0xfbU, 0x01U, 0xf3U, 0xcaU, 0x0eU
  };

static void test_secret_to_public(uint8_t *sk, uint8_t *pk)
{
  uint8_t pk_comp[64U] = { 0U };
  bool b = Hacl_K256_ECDSA_secret_to_public(pk_comp, sk);
  C_String_print("\n Test K256 secret_to_public: ");
  bool is_eq = Lib_PrintBuffer_result_compare_display(64U, pk, pk_comp);
  if (is_eq && b)
  {
    C_String_print("Success!\n");
  }
  else
  {
    C_String_print("Failure :(\n");
    exit((int32_t)255);
  }
}

static void test_verify_sha256(uint32_t msg_len, uint8_t *msg, uint8_t *pk, uint8_t *sgnt)
{
  bool b = Hacl_K256_ECDSA_ecdsa_verify_sha256(msg_len, msg, pk, sgnt);
  C_String_print("\n Test K256 ecdsa verification: ");
  if (b)
  {
    C_String_print("Success!\n");
  }
  else
  {
    C_String_print("Failure :(\n");
    exit((int32_t)255);
  }
}

static void test_verify_hashed(uint8_t *msgHash, uint8_t *pk, uint8_t *sgnt)
{
  bool b = Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(msgHash, pk, sgnt);
  C_String_print("\n Test K256 ecdsa verification: ");
  if (b)
  {
    C_String_print("Success!\n");
  }
  else
  {
    C_String_print("Failure :(\n");
    exit((int32_t)255);
  }
}

static void
test_sign_hashed(uint8_t *msgHash, uint8_t *sk, uint8_t *nonce, uint8_t *expected_sgnt)
{
  uint8_t sgnt[64U] = { 0U };
  KRML_HOST_IGNORE(Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(sgnt, msgHash, sk, nonce));
  C_String_print("\n Test K256 ecdsa signing:\n");
  if (!Lib_PrintBuffer_result_compare_display(64U, sgnt, expected_sgnt))
  {
    exit((int32_t)255);
  }
}

static void
test_sign_and_verify_hashed(
  uint8_t *msgHash,
  uint8_t *sk,
  uint8_t *nonce,
  uint8_t *pk,
  uint8_t *expected_sgnt
)
{
  test_verify_hashed(msgHash, pk, expected_sgnt);
  test_sign_hashed(msgHash, sk, nonce, expected_sgnt);
}

static void test_public_key_compressed(uint8_t *pk)
{
  uint8_t pk_c[33U] = { 0U };
  uint8_t pk_raw_c[64U] = { 0U };
  Hacl_K256_ECDSA_public_key_compressed_from_raw(pk_c, pk);
  bool b = Hacl_K256_ECDSA_public_key_compressed_to_raw(pk_raw_c, pk_c);
  C_String_print("\n Test K256 pk_compressed:\n");
  if (b)
  {
    if (!Lib_PrintBuffer_result_compare_display(64U, pk, pk_raw_c))
    {
      exit((int32_t)255);
    }
  }
  else
  {
    C_String_print("Failure :(\n");
    exit((int32_t)255);
  }
}

static void test_public_key_uncompressed(uint8_t *pk)
{
  uint8_t pk_u[65U] = { 0U };
  uint8_t pk_raw_u[64U] = { 0U };
  Hacl_K256_ECDSA_public_key_uncompressed_from_raw(pk_u, pk);
  bool b = Hacl_K256_ECDSA_public_key_uncompressed_to_raw(pk_raw_u, pk_u);
  C_String_print("\n Test K256 pk_uncompressed:\n");
  if (b)
  {
    if (!Lib_PrintBuffer_result_compare_display(64U, pk, pk_raw_u))
    {
      exit((int32_t)255);
    }
  }
  else
  {
    C_String_print("Failure :(\n");
    exit((int32_t)255);
  }
}

exit_code main(void)
{
  C_String_print("\nTEST 1. K256\n");
  test_verify_sha256(6U, msg1, pk1, sgnt1);
  C_String_print("\nTEST 2. K256\n");
  test_sign_and_verify_hashed(msgHash2, sk2, nonce2, pk2, sgnt2);
  C_String_print("\nTEST 3. K256\n");
  test_public_key_compressed(pk1);
  C_String_print("\nTEST 4. K256\n");
  test_public_key_uncompressed(pk1);
  C_String_print("\nTEST 5. K256\n");
  test_secret_to_public(sk2, pk2);
  return EXIT_SUCCESS;
}

