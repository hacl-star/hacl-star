#include <inttypes.h>
#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include <stdbool.h>
#include "test_helpers.h"
#include "Lib_RandomBuffer_System.h"

#include "arm8_intrinsics.h"
#include "Hacl_IntTypes_Intrinsics.h"

#define TEST_VECTORS 100
#define ROUNDS 10000
#define N_BYTES ROUNDS * 16

typedef struct {
  uint32_t size_a;
  uint32_t size_b;
} test_config;

static test_config tests[] =
  {
   { .size_a = 0,
     .size_b = 1,
   },
   { .size_a = 3,
     .size_b = 3,
   },
   { .size_a = 4,
     .size_b = 5,
   },
   { .size_a = 5,
     .size_b = 4,
   },
   { .size_a = 8,
     .size_b = 8,
   },
  };

void read_random_uint64_t (uint64_t* res, uint32_t size) {
  memset(res, 0x00, 8);
  read_random_bytes(size, res);
  return;
}


int main () {
  uint64_t a, b, cin;
  uint64_t r, r2, cout, cout2;
  bool passed = true;

  cycles c1, c2;
  clock_t t1, t2;

  read_random_uint64_t (&a, 8);
  read_random_uint64_t (&b, 8);
  read_random_uint64_t (&cin, 1);
  cin = cin % 2;
  r = 0U;
  r2 = 0U;

  t1 = clock (); c1 = cpucycles_begin ();
  for (int j = 0; j < ROUNDS; j++)
    cin = uint128_t_add_carry_u64(cin, a, r, &r);
  c2 = cpucycles_end (); t2 = clock ();
  clock_t time_uint128_t_add_carry_u64 = t2 - t1;
  cycles cycles_uint128_t_add_carry_u64 = c2 - c1;
  printf("uint128_t_add_carry_u64:\n");
  print_time(N_BYTES, time_uint128_t_add_carry_u64, cycles_uint128_t_add_carry_u64);
  
  t1 = clock (); c1 = cpucycles_begin ();
  for (int j = 0; j < ROUNDS; j++)
    cin = Hacl_IntTypes_Intrinsics_add_carry_u64(cin, a, r2, &r2);
  c2 = cpucycles_end (); t2 = clock ();
  clock_t time_intrinsics_add_carry_u64 = t2 - t1;
  cycles cycles_intrinsics_add_carry_u64 = c2 - c1;
  printf("Hacl_IntTypes_Intrinsics_add_carry_u64:\n");
  print_time(N_BYTES, time_intrinsics_add_carry_u64, cycles_intrinsics_add_carry_u64);

  t1 = clock (); c1 = cpucycles_begin ();
  for (int j = 0; j < ROUNDS; j++)
    cin = uint128_t_sub_borrow_u64(cin, a, r, &r);
  c2 = cpucycles_end (); t2 = clock ();
  clock_t time_uint128_t_sub_borrow_u64 = t2 - t1;
  cycles cycles_uint128_t_sub_borrow_u64 = c2 - c1;
  printf("uint128_t_sub_borrow_u64:\n");
  print_time(N_BYTES, time_uint128_t_sub_borrow_u64, cycles_uint128_t_sub_borrow_u64);
  
  t1 = clock (); c1 = cpucycles_begin ();
  for (int j = 0; j < ROUNDS; j++)
    cin = Hacl_IntTypes_Intrinsics_sub_borrow_u64(cin, a, r2, &r2);
  c2 = cpucycles_end (); t2 = clock ();
  clock_t time_intrinsics_sub_borrow_u64 = t2 - t1;
  cycles cycles_intrinsics_sub_borrow_u64 = c2 - c1;
  printf("Hacl_IntTypes_Intrinsics_sub_borrow_u64:\n");
  print_time(N_BYTES, time_intrinsics_sub_borrow_u64, cycles_intrinsics_sub_borrow_u64);


  for (int i = 0; i < sizeof(tests)/sizeof(test_config); ++i) {
    for (int j = 0; j < TEST_VECTORS; ++j) {
      read_random_uint64_t (&a, tests[i].size_a);
      read_random_uint64_t (&b, tests[i].size_b);
      read_random_uint64_t (&cin, 1);
      cin = cin % 2;
      r = 0U;
      r2 = 0U;
      cout = uint128_t_add_carry_u64(cin, a, b, &r);
      cout2 = Hacl_IntTypes_Intrinsics_add_carry_u64(cin, a, b, &r2);
      /* printf("(add_carry_u64) Result: %lud Carry: %lud\n", r, c); */

      if (!(r == r2 && cout == cout2)) {
	printf("Test failed for %lud and %lud with carry %lud:\n"
	       "Hacl_IntTypes_Intrinsics_add_carry_u64: result %lud, carry %lud\n"
	       "uint128_t_add_carry:                    result %lud, carry %lud\n",
	       a, b, cin, r2, cout2, r, cout);
	passed = false;
      }

      r = 0U;
      r2 = 0U;
      cout = uint128_t_sub_borrow_u64(cin, a, b, &r);
      cout2 = Hacl_IntTypes_Intrinsics_sub_borrow_u64(cin, a, b, &r2);
      /* printf("(sub_borrow_u64) Result: %lud Carry: %lud\n", r, c); */
      if (!(r == r2 && cout == cout2)) {
	printf("Test failed for %lud and %lud with carry %lud:\n"
	       "Hacl_IntTypes_Intrinsics_sub_borrow_u64: result %lud, carry %lud\n"
	       "uint128_t_sub_borrow:                    result %lud, carry %lud\n",
	       a, b, cin, r2, cout2, r, cout);
	passed = false;
      }
    }
  }
  if (passed)
    return EXIT_SUCCESS;
  else
    return EXIT_FAILURE;
}
