#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <time.h>
#include <stdbool.h>
#include "test_helpers.h"

#include "multiplication.h"

#define ROUNDS 50000000
#define SIZE   16384

int main()
{
  cycles a,b;
	clock_t t1,t2;

  uint64_t arg_a[4U] = { 1, 2, 3, 4 };
  uint64_t arg_b[4U] = { 1, 2, 3, 4 };
  uint64_t arg_t[8U] = { 0U };

  uint64_t arg_t2[8U] = { 0U };
  bench_multiplication_buffer(arg_a, arg_b, arg_t);
  bench_bignum_mul(arg_a, arg_b, arg_t2);
  compare64(8, arg_t, arg_t2);

  /* for (int i = 0; i < 4; i++) */
  /*   printf("%" PRIu64" %" PRIu64"\n", arg_a[i], arg_b[i]); */
  /* bench_multiplication_buffer(arg_a, arg_b, arg_t); */
  /* for (int i = 0; i < 8; i++) */
  /*   printf("%" PRIu64 "\n", arg_t[i]); */

  for (int j = 0; j < ROUNDS; j++)
    bench_multiplication_buffer(arg_a, arg_b, arg_t);

	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
      bench_multiplication_buffer(arg_a, arg_b, arg_t);

	b = cpucycles_end();

	t2 = clock();
	clock_t tdiff1 = t2 - t1;
	cycles cdiff1 = b - a;

	uint64_t count = ROUNDS;
	printf("bench_multiplication_buffer\n");
	print_time(count,tdiff1,cdiff1);

//////////////////////////////////////

  /* bench_bignum_mul(arg_a, arg_b, arg_t); */
  /* for (int i = 0; i < 8; i++) */
  /*   printf("%" PRIu64 "\n", arg_t[i]); */


  for (int j = 0; j < ROUNDS; j++)
    bench_bignum_mul(arg_a, arg_b, arg_t);

	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
      bench_bignum_mul(arg_a, arg_b, arg_t);

	b = cpucycles_end();

	t2 = clock();
	clock_t tdiff2 = t2 - t1;
	cycles cdiff2 = b - a;

	printf("bench_bignum_mul\n");
	print_time(count,tdiff2,cdiff2);

}
