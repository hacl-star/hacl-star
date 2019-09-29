#include "rsa_pss_2048_sha256_mgf1_0_test.h"
#include "rsa_pss_2048_sha256_mgf1_32_test.h"
#include "rsa_pss_3072_sha256_mgf1_32_test.h"
#include "rsa_pss_4096_sha256_mgf1_32_test.h"

// https://github.com/google/wycheproof/tree/master/testvectors

bool
ctest(
  uint32_t modBits,
  uint8_t *n1,
  uint32_t pkeyBits,
  uint8_t *e,
  uint8_t *r2,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t sLen,
  uint32_t sigLen,
  uint8_t *sig
)
{
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  if (8 * nLen != sigLen) { return false; }
  uint32_t eLen = (pkeyBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t pkeyLen = nLen + eLen;
  uint64_t pkey[pkeyLen];
  memset(pkey, 0U, pkeyLen * sizeof pkey[0U]);
  uint64_t *nNat = pkey;
  uint64_t *eNat = pkey + nLen;
  Hacl_Bignum_Convert_bn_from_bytes_be((modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, n1, nNat);
  Hacl_Bignum_Convert_bn_from_bytes_be((pkeyBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, e, eNat);
  uint64_t r2Nat[nLen];
  memset(r2Nat, 0U, nLen * sizeof r2Nat[0U]);
  Hacl_Bignum_Convert_bn_from_bytes_be((modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, r2, r2Nat);

  bool verify_sgnt = rsapss_verify(modBits, pkeyBits, pkey, r2Nat, sLen, sig, msgLen, msg);
  return verify_sgnt;
}


int main () {
  int test0 = main_rsa_pss_2048_sha256_mgf1_0_test();
  printf ("\n rsa_pss_2048_sha256_mgf1_0_test: %d \n", test0);
  int test1 = main_rsa_pss_2048_sha256_mgf1_32_test();
  printf ("\n rsa_pss_2048_sha256_mgf1_32_test: %d \n", test1);
  int test2 = main_rsa_pss_3072_sha256_mgf1_32_test();
  printf ("\n rsa_pss_3072_sha256_mgf1_32_test: %d \n", test2);
  int test3 = main_rsa_pss_4096_sha256_mgf1_32_test();
  printf ("\n rsa_pss_4096_sha256_mgf1_32_test: %d \n", test3);

  int res = test0 && test1 && test2 && test3;
  if (res)
  {
    printf("SUCCESS\n");
  }
  else
  {
    printf("Test failed\n");
  }

  return 1;
}
