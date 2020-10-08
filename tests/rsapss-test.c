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

bool print_result(uint32_t len, uint8_t* comp, uint8_t* exp) {
  return compare_and_print(len, comp, exp);
}

bool print_test(
  uint32_t modBits,
  uint8_t *nb,
  uint32_t eBits,
  uint8_t *eb,
  uint32_t dBits,
  uint8_t *db,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t saltLen,
  uint8_t *salt,
  uint8_t *sgnt_expected
){
  uint32_t nbLen = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint8_t sgnt[nbLen];
  memset(sgnt, 0U, nbLen * sizeof (sgnt[0U]));

  uint64_t *pkey = Hacl_RSAPSS_new_rsapss_load_pkey(modBits, eBits, nb, eb);
  uint64_t *skey = Hacl_RSAPSS_new_rsapss_load_skey(modBits, eBits, dBits, nb, eb, db);


  Hacl_RSAPSS_rsapss_sign(Spec_Hash_Definitions_SHA2_256, modBits, eBits, dBits, skey, saltLen, salt, msgLen, msg, sgnt);
  printf("RSAPSS sign Result:\n");
  bool ok = print_result(nbLen, sgnt, sgnt_expected);

  printf("RSAPSS verify Result:\n");
  bool ver = Hacl_RSAPSS_rsapss_verify(Spec_Hash_Definitions_SHA2_256, modBits, eBits, pkey, saltLen, nbLen, sgnt, msgLen, msg);
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
