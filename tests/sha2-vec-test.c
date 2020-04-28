#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <stdbool.h>
#include "Hacl_Hash.h"
#include "Hacl_Impl_SHA2_Core.h"

#include "test_helpers.h"


bool print_result(uint8_t* comp, uint8_t* exp, int len) {
  return compare_and_print(len, comp, exp);
}

bool print_test(){
  int in_len = 71;

  uint8_t in[71] = {0};
  uint8_t in1[71] = {0};
  uint8_t in2[71] = {0};
  uint8_t in3[71] = {0};
  uint8_t in4[71] = {0};
  uint8_t in5[71] = {0};
  uint8_t in6[71] = {0};
  uint8_t in7[71] = {0};

  in1[0] = 1;
  in2[0] = 2;
  in3[0] = 3;
  in4[0] = 4;
  in5[0] = 5;
  in6[0] = 6;
  in7[0] = 7;

  uint8_t exp[64] = {0};
  uint8_t exp1[64] = {0};
  uint8_t exp2[64] = {0};
  uint8_t exp3[64] = {0};
  uint8_t exp4[64] = {0};
  uint8_t exp5[64] = {0};
  uint8_t exp6[64] = {0};
  uint8_t exp7[64] = {0};

  uint8_t comp[64] = {0};
  uint8_t comp1[64] = {0};
  uint8_t comp2[64] = {0};
  uint8_t comp3[64] = {0};
  uint8_t comp4[64] = {0};
  uint8_t comp5[64] = {0};
  uint8_t comp6[64] = {0};
  uint8_t comp7[64] = {0};

  bool ok = true;


  Hacl_Hash_SHA2_hash_256(in,in_len,exp);
  Hacl_Hash_SHA2_hash_256(in1,in_len,exp1);
  Hacl_Hash_SHA2_hash_256(in2,in_len,exp2);
  Hacl_Hash_SHA2_hash_256(in3,in_len,exp3);
  Hacl_Hash_SHA2_hash_256(in4,in_len,exp4);
  Hacl_Hash_SHA2_hash_256(in5,in_len,exp5);
  Hacl_Hash_SHA2_hash_256(in6,in_len,exp6);
  Hacl_Hash_SHA2_hash_256(in7,in_len,exp7);


  Hacl_Impl_SHA2_Core_sha256(comp,in_len,in);
  printf("NEW SHA2-256 (32-bit) Result:\n");
  ok = print_result(comp, exp, 32) && ok;

  Hacl_Impl_SHA2_Core_sha256_4(comp,comp1,comp2,comp3,in_len,in,in1,in2,in3);
  printf("VEC4 SHA2-256 (32-bit) Result:\n");
  ok = print_result(comp, exp,32) && ok;
  ok = print_result(comp1, exp1,32) && ok;
  ok = print_result(comp2, exp2,32) && ok;
  ok = print_result(comp3, exp3,32) && ok;

  Hacl_Impl_SHA2_Core_sha256_8(comp,comp1,comp2,comp3,comp4,comp5,comp6,comp7,in_len,in,in1,in2,in3,in4,in5,in6,in7);
  printf("VEC8 SHA2-256 (32-bit) Result:\n");
  ok = print_result(comp, exp,32) && ok;
  ok = print_result(comp1, exp1,32) && ok;
  ok = print_result(comp2, exp2,32) && ok;
  ok = print_result(comp3, exp3,32) && ok;
  ok = print_result(comp4, exp4,32) && ok;
  ok = print_result(comp5, exp5,32) && ok;
  ok = print_result(comp6, exp6,32) && ok;
  ok = print_result(comp7, exp7,32) && ok;

  return ok;
}

int main()
{
  bool ok = print_test();

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
