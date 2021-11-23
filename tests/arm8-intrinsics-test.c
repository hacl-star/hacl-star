#include <inttypes.h>
#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include <stdbool.h>
#include "test_helpers.h"

#include "arm8-intrinsics_vectors.h"

#include "arm8_intrinsics.h"
#include "Hacl_IntTypes_Intrinsics.h"

#define ROUNDS 10000
#define N_BYTES ROUNDS * 16

int main () {
  uint64_t a, b, cin;
  uint64_t r, r2, cout, cout2;
  bool passed = true;

  cycles c1, c2;
  clock_t t1, t2;

  a = a_vectors[num_vectors - 1];
  b = b_vectors[num_vectors - 1];
  cin = cin_vectors[num_vectors - 1];
  r = 0U;
  r2 = 0U;

  t1 = clock (); c1 = cpucycles_begin ();
  for (int j = 0; j < ROUNDS; j++)
    cin = uint128_t_add_carry_u64(cin, a, r, &r);
  c2 = cpucycles_end (); t2 = clock ();
  clock_t time_uint128_t_add_carry_u64 = t2 - t1;
  cycles cycles_uint128_t_add_carry_u64 = c2 - c1;
  printf("uint128_t_add_carry_u64:\n");
  print_time(N_BYTES,
             time_uint128_t_add_carry_u64,
             cycles_uint128_t_add_carry_u64);

  t1 = clock (); c1 = cpucycles_begin ();
  for (int j = 0; j < ROUNDS; j++)
    cin = Hacl_IntTypes_Intrinsics_add_carry_u64(cin, a, r2, &r2);
  c2 = cpucycles_end (); t2 = clock ();
  clock_t time_intrinsics_add_carry_u64 = t2 - t1;
  cycles cycles_intrinsics_add_carry_u64 = c2 - c1;
  printf("Hacl_IntTypes_Intrinsics_add_carry_u64:\n");
  print_time(N_BYTES,
             time_intrinsics_add_carry_u64,
             cycles_intrinsics_add_carry_u64);

  t1 = clock (); c1 = cpucycles_begin ();
  for (int j = 0; j < ROUNDS; j++)
    cin = uint128_t_sub_borrow_u64(cin, a, r, &r);
  c2 = cpucycles_end (); t2 = clock ();
  clock_t time_uint128_t_sub_borrow_u64 = t2 - t1;
  cycles cycles_uint128_t_sub_borrow_u64 = c2 - c1;
  printf("uint128_t_sub_borrow_u64:\n");
  print_time(N_BYTES,
             time_uint128_t_sub_borrow_u64,
             cycles_uint128_t_sub_borrow_u64);

  t1 = clock (); c1 = cpucycles_begin ();
  for (int j = 0; j < ROUNDS; j++)
    cin = Hacl_IntTypes_Intrinsics_sub_borrow_u64(cin, a, r2, &r2);
  c2 = cpucycles_end (); t2 = clock ();
  clock_t time_intrinsics_sub_borrow_u64 = t2 - t1;
  cycles cycles_intrinsics_sub_borrow_u64 = c2 - c1;
  printf("Hacl_IntTypes_Intrinsics_sub_borrow_u64:\n");
  print_time(N_BYTES,
             time_intrinsics_sub_borrow_u64,
             cycles_intrinsics_sub_borrow_u64);


  for (int i = 0; i < num_vectors; ++i) {
    r = 0U;
    r2 = 0U;
    cout = uint128_t_add_carry_u64
      (cin_vectors[i], a_vectors[i], b_vectors[i], &r);
    cout2 = Hacl_IntTypes_Intrinsics_add_carry_u64
      (cin_vectors[i],a_vectors[i], b_vectors[i], &r2);
    if (!(r == r2 && cout == cout2 &&
          r == addcarry_res_vectors[i] &&
          cout == addcarry_cout_vectors[i])) {
      printf("Test failed for %" PRIu64 " and %" PRIu64 " \
with carry %" PRIu64 ":\n\
Hacl_IntTypes_Intrinsics_add_carry_u64: res %" PRIu64 ", carry %" PRIu64 "\n\
uint128_t_add_carry:                    res %" PRIu64 ", carry %" PRIu64 "\n",
             a_vectors[i], b_vectors[i], cin_vectors[i], r2, cout2, r, cout);
      passed = false;
    }

    r = 0U;
    r2 = 0U;
    cout = uint128_t_sub_borrow_u64
      (cin_vectors[i], a_vectors[i], b_vectors[i], &r);
    cout2 = Hacl_IntTypes_Intrinsics_sub_borrow_u64
      (cin_vectors[i],a_vectors[i], b_vectors[i], &r2);
    if (!(r == r2 && cout == cout2 &&
          r == subborrow_res_vectors[i] &&
          cout == subborrow_cout_vectors[i])) {
      printf("Test failed for %" PRIu64 " and %" PRIu64 " \
with carry %" PRIu64 ":\n\
Hacl_IntTypes_Intrinsics_sub_borrow_u64: res %" PRIu64 ", carry %" PRIu64 "\n\
uint128_t_sub_borrow:                    res %" PRIu64 ", carry %" PRIu64 "\n",
             a_vectors[i], b_vectors[i], cin_vectors[i], r2, cout2, r, cout);
      passed = false;
    }
  }
  if (passed)
    return EXIT_SUCCESS;
  else
    return EXIT_FAILURE;
}
