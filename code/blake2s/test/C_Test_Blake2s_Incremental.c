#include "blake2.h"
#include "blake2-impl.h"
#include "C_Test_Blake2s_Incremental.h"
#include "c/Lib_RandomBuffer_System.h"


uint8_t Lib_PrintBuffer_compare_fast(uint32_t len, uint8_t* buffer1, uint8_t* buffer2) {
  uint8_t res = 0;
  uint32_t i;
  for (i = 0; i < len; i++) {
    res |= buffer1[i] ^ buffer2[i];
  }
  return res;
}

uint8_t Lib_PrintBuffer_compare(uint32_t len, uint8_t* buffer1, uint8_t* buffer2) {
  uint8_t res = 0;
  uint32_t i;
  for (i = 0; i < len; i++) {
    res |= buffer1[i] ^ buffer2[i];
  }
  if (res == 0) {
    printf("Success !\n\n");
  } else {
    printf("Failure !\n\n");
  }
  return res;
}

uint8_t Lib_PrintBuffer_compare_display(uint32_t len, uint8_t* buffer1, uint8_t* buffer2) {
  uint8_t res = 0;
  uint32_t i;
  Lib_PrintBuffer_print_compare(len, buffer1, buffer2);
  for (i = 0; i < len; i++) {
    res |= buffer1[i] ^ buffer2[i];
  }
  if (res == 0) {
    printf("Success !\n\n");
  } else {
    printf("Failure !\n\n");
  }
  return res;
}


exit_code main()
{

  C_String_print("\n");

  /* Length of the input */
  size_t len = 2999;
  size_t keylen = 2999;
  size_t outlen = 32;

  /* Allocating space for random input */
  uint8_t *zeros = malloc(len * sizeof(uint8_t));
  uint8_t *input = malloc(len * sizeof(uint8_t));
  uint8_t *key = malloc(keylen * sizeof(uint8_t));
  uint8_t *outr = malloc(outlen * sizeof(uint8_t));
  uint8_t *outh = malloc(outlen * sizeof(uint8_t));

  /* Setting zeros */
  memset(zeros, 0, len);
  memset(input, 0, len);
  memset(key, 0, keylen);
  memset(outr, 0, outlen);
  memset(outh, 0, outlen);

  /* Setting the input and key to a random values */
  bool ires0 = randombytes(input, len);
  bool ires1 = randombytes(key, keylen);

  /* Display input */
  //Lib_PrintBuffer_print_bytes(len, input);

  /* Control: the input is equal to itself */
  C_String_print("Control (Success)... ");
  bool cres0 = Lib_PrintBuffer_compare(len, input, input);

  /* Control: the input is equal to itself */
  C_String_print("Control (Failure)... ");
  bool cres1 = Lib_PrintBuffer_compare(len, input, zeros);

  /* Perform multiple tests */
  uint8_t result = 0;
  uint32_t i,ll,kl,nn;
  for (i = 0; i < 1; i++) {
    for (ll = 0; ll < 2999; ll++) { // This fail abnormally for all values where ll % 128 = 0 /\ ll <> 0.
      for (kl = 0; kl < 32; kl++) { // This seems to fail ?abnormally? for 33 < kl
        for (nn = 1; nn < outlen + 1; nn++) { // This seems to normally fail for 64 <= nn.
          /* memset(input, 0, len); */
          /* memset(key, 0, keylen); */
          /* memset(outr, 0, outlen); */
          /* memset(outh, 0, outlen); */

          /* Setting the input and key to a random values */
          bool ires0 = randombytes(input, ll);
          bool ires1 = randombytes(key, kl);

          /* Testing the computation of Blake2s */
          int ignored = ref_blake2s(outr, nn, input, ll, key, kl);
          Hacl_Blake2s_blake2s(nn, outh, ll, input, kl, key);

          /* Display output */
          C_String_print("Test ... ");
          printf("ll=%d; kl=%d; nn=%d\n", ll, kl, nn);
          /* Lib_PrintBuffer_print_bytes(outlen, outr); */
          /* Lib_PrintBuffer_print_bytes(outlen, outh); */
          /* result |= Lib_PrintBuffer_compare_fast(outlen, outh, outr); */
          result |= Lib_PrintBuffer_compare_display(nn, outh, outr);
        }
      }
    }
  }

  /* Test for failure */
  if (result == 0) {
    C_String_print("\nComposite Success !!\n");
  } else {
    C_String_print("\nComposite Failure !!\n");
  }

  return EXIT_SUCCESS;
}
