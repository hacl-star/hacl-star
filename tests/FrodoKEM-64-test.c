#include "Hacl_Frodo64.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <inttypes.h>

#include "test_helpers.h"
#include "FrodoKEM-64_vectors.h"

bool test_dec(uint8_t *sk, uint8_t *ct, uint8_t *ss_expected){
  uint8_t ss2[16U];
  Hacl_Frodo64_crypto_kem_dec(ss2, ct, sk);
  bool ok = compare_and_print(16, ss2, ss_expected);
  return ok;
}


bool
test_frodo()
{
  uint8_t pk[976U];
  uint8_t sk[2032U];
  uint8_t ct[1080U];
  uint8_t ss1[16U];
  uint8_t ss2[16U];

  Hacl_Frodo64_crypto_kem_keypair(pk, sk);
  Hacl_Frodo64_crypto_kem_enc(ct, ss1, pk);
  Hacl_Frodo64_crypto_kem_dec(ss2, ct, sk);

  for (int i = 0; i < 16; i++) {
      if (ss1[i] != ss2[i]) {
        return false;
      }
  }

  return true;
}

int main()
{
  bool pass = test_frodo();
  if (pass)
    {
      printf("[FrodoKEM] Self-test: PASS\n");
    }
  else
    {
      printf("[FrodoKEM] Self-test: FAIL\n");
    }

  for (int i = 0; i < sizeof(vectors)/sizeof(frodo_test_vector); ++i) {
    pass &= test_dec(vectors[i].sk,vectors[i].ct,vectors[i].ss);
  }

  if (pass) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
