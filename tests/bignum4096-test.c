#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Hacl_Bignum4096.h"

#include "bignum4096_vectors.h"
#include "test_helpers.h"

bool
mod_exp_bytes_be_precomp(uint8_t* nBytes,
                         uint8_t* aBytes,
                         uint32_t bBits,
                         uint8_t* bBytes,
                         uint8_t* resBytes)
{
  uint64_t res[64U] = { 0 };
  uint32_t bBytesLen = (bBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;

  uint64_t* a = Hacl_Bignum4096_new_bn_from_bytes_be(512, aBytes);
  uint64_t* n = Hacl_Bignum4096_new_bn_from_bytes_be(512, nBytes);
  uint64_t* b = Hacl_Bignum4096_new_bn_from_bytes_be(bBytesLen, bBytes);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64* k =
    Hacl_Bignum4096_mont_ctx_init(n);

  Hacl_Bignum4096_mod_exp_vartime_precomp(k, a, bBits, b, res);
  Hacl_Bignum4096_bn_to_bytes_be(res, resBytes);

  Hacl_Bignum4096_mont_ctx_free(k);
  return 1;
}

bool
mod_exp_bytes_be(uint8_t* nBytes,
                 uint8_t* aBytes,
                 uint32_t bBits,
                 uint8_t* bBytes,
                 uint8_t* resBytes)
{
  uint64_t res[64U] = { 0 };
  uint32_t bBytesLen = (bBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;

  uint64_t* a = Hacl_Bignum4096_new_bn_from_bytes_be(512, aBytes);
  uint64_t* n = Hacl_Bignum4096_new_bn_from_bytes_be(512, nBytes);
  uint64_t* b = Hacl_Bignum4096_new_bn_from_bytes_be(bBytesLen, bBytes);

  Hacl_Bignum4096_mod_exp_vartime(n, a, bBits, b, res);
  Hacl_Bignum4096_bn_to_bytes_be(res, resBytes);

  return 1;
}

bool
print_test_bytes_be_precomp(uint8_t* nBytes,
                            uint8_t* aBytes,
                            uint32_t bBits,
                            uint8_t* bBytes,
                            uint8_t* resBytes_expected)
{
  uint8_t resBytes[512U] = { 0 };
  bool ok = mod_exp_bytes_be_precomp(nBytes, aBytes, bBits, bBytes, resBytes);
  printf("\n mod_exp_precomp for bytes Result: \n");
  ok = ok && compare_and_print(512U, resBytes, resBytes_expected);

  return ok;
}

bool
print_test_bytes_be(uint8_t* nBytes,
                    uint8_t* aBytes,
                    uint32_t bBits,
                    uint8_t* bBytes,
                    uint8_t* resBytes_expected)
{
  uint8_t resBytes[512U] = { 0 };
  bool ok = mod_exp_bytes_be(nBytes, aBytes, bBits, bBytes, resBytes);
  printf("\n mod_exp for bytes Result: \n");
  ok = ok && compare_and_print(512U, resBytes, resBytes_expected);

  return ok;
}

bool
print_test(uint64_t* n,
           uint64_t* a,
           uint32_t bBits,
           uint64_t* b,
           uint64_t* res_expected)
{
  uint64_t res[64U] = { 0 };
  Hacl_Bignum4096_mod_exp_vartime(n, a, bBits, b, res);
  printf("\n mod_exp Result: \n");

  bool ok = true;
  for (size_t i = 0; i < 64U; i++)
    ok = ok & (res_expected[i] == res[i]);
  if (ok)
    printf("Success!\n");
  else
    printf("**FAILED**\n");

  return ok;
}

int
main()
{

  bool ok = true;
  for (int i = 0;
       i < sizeof(vectors_be) / sizeof(bignum4096_bytes_be_test_vector);
       ++i) {
    ok &= print_test_bytes_be_precomp(vectors_be[i].nBytes,
                                      vectors_be[i].aBytes,
                                      vectors_be[i].bBits,
                                      vectors_be[i].bBytes,
                                      vectors_be[i].resBytes);
  }

  for (int i = 0;
       i < sizeof(vectors_be) / sizeof(bignum4096_bytes_be_test_vector);
       ++i) {
    ok &= print_test_bytes_be(vectors_be[i].nBytes,
                              vectors_be[i].aBytes,
                              vectors_be[i].bBits,
                              vectors_be[i].bBytes,
                              vectors_be[i].resBytes);
  }

  for (int i = 0; i < sizeof(vectors) / sizeof(bignum4096_test_vector); ++i) {
    ok &= print_test(vectors[i].n,
                     vectors[i].a,
                     vectors[i].bBits,
                     vectors[i].b,
                     vectors[i].res);
  }

  if (ok)
    return EXIT_SUCCESS;
  else
    return EXIT_FAILURE;
}
