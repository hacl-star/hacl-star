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
//////////////////////////////////////

  for (int j = 0; j < ROUNDS; j++)
    bench_unroll1_bignum_mul(arg_a, arg_b, arg_t);

  t1 = clock();
  a = cpucycles_begin();

  for (int j = 0; j < ROUNDS; j++)
    bench_unroll1_bignum_mul(arg_a, arg_b, arg_t);

  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff21 = t2 - t1;
  cycles cdiff21 = b - a;

  printf("bench_unroll1_bignum_mul\n");
  print_time(count,tdiff21,cdiff21);

/////////////////////////////////////////

  for (int j = 0; j < ROUNDS; j++)
    bench_bignum_sqr(arg_a, arg_t);

	t1 = clock();
  a = cpucycles_begin();

  for (int j = 0; j < ROUNDS; j++)
    bench_bignum_sqr(arg_a, arg_t);

	b = cpucycles_end();

	t2 = clock();
	clock_t tdiff3 = t2 - t1;
	cycles cdiff3 = b - a;

	printf("bench_bignum_sqr\n");
	print_time(count,tdiff3,cdiff3);



  for (int j = 0; j < ROUNDS; j++)
    bench_sq(arg_a, arg_t);

	t1 = clock();
  a = cpucycles_begin();

  for (int j = 0; j < ROUNDS; j++)
    bench_sq(arg_a, arg_t);

	b = cpucycles_end();

	t2 = clock();
	clock_t tdiff4 = t2 - t1;
	cycles cdiff4 = b - a;

	printf("bench_sq\n");
	print_time(count,tdiff4,cdiff4);


//////////////////////////////////////

  for (int j = 0; j < ROUNDS; j++)
    bench_bignum_reduction(arg_t, arg_a);

	t1 = clock();
  a = cpucycles_begin();

  for (int j = 0; j < ROUNDS; j++)
    bench_bignum_reduction(arg_t, arg_a);

	b = cpucycles_end();

	t2 = clock();
	clock_t tdiff5 = t2 - t1;
	cycles cdiff5 = b - a;

	printf("bench_bignum_reduction\n");
	print_time(count,tdiff5,cdiff5);


  for (int j = 0; j < ROUNDS; j++)
    bench_montgomery_reduction_buffer(arg_t, arg_a);

	t1 = clock();
  a = cpucycles_begin();

  for (int j = 0; j < ROUNDS; j++)
    bench_montgomery_reduction_buffer(arg_t, arg_a);

	b = cpucycles_end();

	t2 = clock();
	clock_t tdiff6 = t2 - t1;
	cycles cdiff6 = b - a;

	printf("bench_montgomery_reduction_buffer\n");
	print_time(count,tdiff6,cdiff6);

////////////////////////////////////

  for (int j = 0; j < ROUNDS; j++)
    bench_bignum_mont_sqr_u64(arg_a, arg_b);

	t1 = clock();
  a = cpucycles_begin();

  for (int j = 0; j < ROUNDS; j++)
    bench_bignum_mont_sqr_u64(arg_a, arg_b);

	b = cpucycles_end();

	t2 = clock();
	clock_t tdiff9 = t2 - t1;
	cycles cdiff9 = b - a;

	printf("bench_bignum_mont_sqr_u64\n");
	print_time(count,tdiff9,cdiff9);


  for (int j = 0; j < ROUNDS; j++)
    bench_bignum_mont_sqr_u64_p256(arg_a, arg_b);

	t1 = clock();
  a = cpucycles_begin();

  for (int j = 0; j < ROUNDS; j++)
    bench_bignum_mont_sqr_u64_p256(arg_a, arg_b);

	b = cpucycles_end();

	t2 = clock();
	clock_t tdiff8 = t2 - t1;
	cycles cdiff8 = b - a;

	printf("bench_bignum_mont_sqr_u64_p256\n");
	print_time(count,tdiff8,cdiff8);


  for (int j = 0; j < ROUNDS; j++)
    bench_mont_sqr_u64_p256(arg_a, arg_b);

	t1 = clock();
  a = cpucycles_begin();

  for (int j = 0; j < ROUNDS; j++)
    bench_mont_sqr_u64_p256(arg_a, arg_b);

	b = cpucycles_end();

	t2 = clock();
	clock_t tdiff7 = t2 - t1;
	cycles cdiff7 = b - a;

	printf("bench_mont_sqr_u64_p256\n");
	print_time(count,tdiff7,cdiff7);


////////////////////////////////////

  for (int j = 0; j < ROUNDS; j++)
    bench_bignum_mul_red(arg_a, arg_b);

	t1 = clock();
  a = cpucycles_begin();

  for (int j = 0; j < ROUNDS; j++)
    bench_bignum_mul_red(arg_a, arg_b);

	b = cpucycles_end();

	t2 = clock();
	clock_t tdiff10 = t2 - t1;
	cycles cdiff10 = b - a;

	printf("bench_bignum_mul_red\n");
	print_time(count,tdiff10,cdiff10);


  for (int j = 0; j < ROUNDS; j++)
    bench_bignum_mul_red_p256(arg_a, arg_b);

	t1 = clock();
  a = cpucycles_begin();

  for (int j = 0; j < ROUNDS; j++)
    bench_bignum_mul_red_p256(arg_a, arg_b);

	b = cpucycles_end();

	t2 = clock();
	clock_t tdiff11 = t2 - t1;
	cycles cdiff11 = b - a;

	printf("bench_bignum_mul_red_p256\n");
	print_time(count,tdiff11,cdiff11);


  for (int j = 0; j < ROUNDS; j++)
    bench_mul_red_p256(arg_a, arg_b);

	t1 = clock();
  a = cpucycles_begin();

  for (int j = 0; j < ROUNDS; j++)
    bench_mul_red_p256(arg_a, arg_b);

	b = cpucycles_end();

	t2 = clock();
	clock_t tdiff12 = t2 - t1;
	cycles cdiff12 = b - a;

	printf("bench_mul_red_p256\n");
	print_time(count,tdiff12,cdiff12);
}
