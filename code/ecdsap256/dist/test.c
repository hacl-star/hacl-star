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

#include "Hacl_P256.h"


#define SIZE   32
#define ROUNDS 100

int main()
{
	cycles a,b;
	clock_t t1,t2;
	uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 32);

	uint64_t len = SIZE;

	uint8_t scalar[SIZE];
	memset(scalar,'P',SIZE);
	
  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_i(result, scalar);

	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_i(result, scalar);
	
	b = cpucycles_end();
	
	t2 = clock();
	clock_t tdiff1 = t2 - t1;
	cycles cdiff1 = b - a;



	uint64_t count = ROUNDS * SIZE;
	printf("Hacl DH_I PERF: %d\n"); 
	print_time(count,tdiff1,cdiff1);



}