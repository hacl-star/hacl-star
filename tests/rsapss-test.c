#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <time.h>

#include "Hacl_RSAPSS.h"

#include "test_helpers.h"
#include "rsapss_vectors.h"


bool hacl_sign(
  uint32_t modBits,
  uint8_t *n1,
  uint32_t pkeyBits,
  uint8_t *e,
  uint32_t skeyBits,
  uint8_t *d,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t saltLen,
  uint8_t *salt,
  uint8_t *sgnt
)
{
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (pkeyBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t dLen = (skeyBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t pkeyLen = nLen + eLen;
  uint32_t skeyLen = pkeyLen + dLen;

  uint64_t skey[skeyLen];
  memset(skey, 0U, skeyLen * sizeof (skey[0U]));
  uint64_t *pkey = skey;
  uint64_t *nNat = skey;
  uint64_t *eNat = skey + nLen;
  uint64_t *dNat = skey + pkeyLen;
  Hacl_Bignum_Convert_bn_from_bytes_be((modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, n1, nNat);
  Hacl_Bignum_Convert_bn_from_bytes_be((pkeyBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, e, eNat);
  Hacl_Bignum_Convert_bn_from_bytes_be((skeyBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, d, dNat);
  Hacl_RSAPSS_rsapss_sign(modBits, pkeyBits, skeyBits, skey, saltLen, salt, msgLen, msg, sgnt);
  return 1;
}

bool hacl_verify(
  uint32_t modBits,
  uint8_t *n1,
  uint32_t pkeyBits,
  uint8_t *e,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t saltLen,
  uint8_t *sgnt
)
{
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (pkeyBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t pkeyLen = nLen + eLen + nLen;

  uint64_t pkey[pkeyLen];
  memset(pkey, 0U, pkeyLen * sizeof pkey[0U]);
  uint64_t *nNat = pkey;
  uint64_t *eNat = pkey + nLen;
  Hacl_Bignum_Convert_bn_from_bytes_be((modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, n1, nNat);
  Hacl_Bignum_Convert_bn_from_bytes_be((pkeyBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, e, eNat);

  bool verify_sgnt = Hacl_RSAPSS_rsapss_verify(modBits, pkeyBits, pkey, saltLen, sgnt, msgLen, msg);
  return verify_sgnt;
}

bool print_result(uint32_t len, uint8_t* comp, uint8_t* exp) {
  return compare_and_print(len, comp, exp);
}

bool print_test(
  uint32_t modBits,
  uint8_t *n1,
  uint32_t pkeyBits,
  uint8_t *e,
  uint32_t skeyBits,
  uint8_t *d,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t saltLen,
  uint8_t *salt,
  uint8_t *sgnt_expected
){
  uint32_t nTLen = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint8_t sgnt[nTLen];
  memset(sgnt, 0U, nTLen * sizeof (sgnt[0U]));
  bool ok = hacl_sign(modBits, n1, pkeyBits, e, skeyBits, d, msgLen, msg, saltLen, salt, sgnt);
  printf("RSAPSS sign Result:\n");
  ok = ok && print_result(nTLen, sgnt, sgnt_expected);

  printf("RSAPSS verify Result:\n");
  bool ver = hacl_verify(modBits, n1, pkeyBits, e, msgLen, msg, saltLen, sgnt);
  if (ver) printf("Success!\n");
  ok = ok && ver;
  return ok;
}

int main() {

  bool ok = true;
  for (int i = 0; i < sizeof(vectors)/sizeof(rsapss_test_vector); ++i) {
    ok &= print_test(vectors[i].modBits,vectors[i].n,vectors[i].eBits,vectors[i].e,vectors[i].dBits,vectors[i].d,
		     vectors[i].msgLen,vectors[i].msg,vectors[i].saltLen,vectors[i].salt,vectors[i].sgnt_expected);
  }

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
