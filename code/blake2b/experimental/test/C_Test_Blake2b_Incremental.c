#include "blake2.h"
#include "blake2-impl.h"
#include "C_Test_Blake2b_Incremental.h"
#include "c/Lib_RandomBuffer_System.h"

bool
test_hacl_blake2b(uint32_t ll, uint8_t *d, uint32_t kk, uint8_t *k, uint32_t nn, uint8_t *expected)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), ll);
  uint8_t tmsg[ll];
  memset(tmsg, 0U, ll * sizeof tmsg[0U]);
  for (uint32_t i = (uint32_t)0U; i < ll; i = i + (uint32_t)1U)
  {
    uint8_t *os = tmsg;
    uint8_t x = d[i];
    os[i] = x;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), kk);
  uint8_t tkey[kk];
  memset(tkey, 0U, kk * sizeof tkey[0U]);
  for (uint32_t i = (uint32_t)0U; i < kk; i = i + (uint32_t)1U)
  {
    uint8_t *os = tkey;
    uint8_t x = k[i];
    os[i] = x;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), nn);
  uint8_t output[nn];
  memset(output, 0U, nn * sizeof output[0U]);
  uint64_t buf0[8U] = { 0U };
  uint32_t buf1 = (uint32_t)0U;
  uint32_t buf2 = (uint32_t)0U;
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)16U * (uint32_t)8U);
  uint8_t buf[(uint32_t)16U * (uint32_t)8U];
  memset(buf, 0U, (uint32_t)16U * (uint32_t)8U * sizeof buf[0U]);
  Hacl_Impl_Blake2b_Incremental_state_r
  state = { .hash = buf0, .n = &buf1, .pl = &buf2, .block = buf };
  Hacl_Impl_Blake2b_Incremental_blake2b_incremental_init(state, kk, k, nn);
  bool res = Hacl_Impl_Blake2b_Incremental_blake2b_incremental_update(state, ll, d);
  Hacl_Impl_Blake2b_Incremental_blake2b_incremental_finish(nn, output, state);
  Lib_PrintBuffer_print_compare_display(nn, output, expected);
  return res;
}


bool Lib_PrintBuffer_compare(uint32_t len, uint8_t* buffer1, uint8_t* buffer2) {
  uint8_t res = 0;
  uint32_t i;
  for (i = 0; i < len; i++) {
    res |= buffer1[i] ^ buffer2[i];
  }
  if (res == 0) {
    printf("Success !\n");
  } else {
    printf("Failure !\n");
  }
  return res;
}

uint8_t Lib_PrintBuffer_result_compare(uint32_t len, uint8_t* buffer1, uint8_t* buffer2) {
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

uint8_t Lib_PrintBuffer_result_compare_display2(uint32_t len, uint8_t* buffer1, uint8_t* buffer2) {
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
  size_t len = 123456;
  size_t keylen = 27;
  size_t outlen = 64;

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
  uint32_t i;
  for (i = 0; i < 100; i++) {
    /* memset(input, 0, len); */
    /* memset(key, 0, keylen); */
    /* memset(outr, 0, outlen); */
    /* memset(outh, 0, outlen); */

    /* Setting the input and key to a random values */
    bool ires0 = randombytes(input, len);
    bool ires1 = randombytes(key, keylen);

    /* Testing the computation of Blake2b */
    int ignored = ref_blake2b(outr, outlen, input, len, key, keylen);
    Hacl_Blake2b_blake2b(outlen, outh, len, input, keylen, key);

    /* Display output */
    C_String_print("Test ...\n");
    /* Lib_PrintBuffer_print_bytes(outlen, outr); */
    /* Lib_PrintBuffer_print_bytes(outlen, outh); */
    result |= Lib_PrintBuffer_result_compare_display2(outlen, outh, outr);
  }

  /* Test for failure */
  if (result == 0) {
    C_String_print("\nComposite Success !!\n");
  } else {
    C_String_print("\nComposite Failure !!\n");
  }

  return EXIT_SUCCESS;
}
