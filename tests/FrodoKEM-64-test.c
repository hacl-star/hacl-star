#include "Hacl_Frodo_KEM.h"
#include <stdio.h>
#include <stdbool.h>

bool
test_frodo()
{
  uint8_t pk[976U];
  uint8_t sk[2016U];
  uint8_t ct[1096U];
  uint8_t ss1[16U];
  uint8_t ss2[16U];
 
  Hacl_Frodo_KEM_crypto_kem_keypair(pk, sk);
  Hacl_Frodo_KEM_crypto_kem_enc(ct, ss1, pk);
  Hacl_Frodo_KEM_crypto_kem_dec(ss2, ct, sk);
  
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
  
  return 0;
}
