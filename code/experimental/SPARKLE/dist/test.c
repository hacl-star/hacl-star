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

#include "Hacl_Impl_Sparkle.h"
#include "test_implementation.c"

#include <stdint.h>
#include <string.h>
#include <stdint.h>

#define ROUNDS 10000

static inline void print(size_t len, uint8_t* comp) {
  for (size_t i = 0; i < len; i++)
    printf("%02x",comp[i]);
  printf("\n");
}



int main(int argc, char const *argv[])
{

	uint32_t* input = (uint32_t*) malloc (sizeof (uint32_t) * 8);
	uint32_t* expected_output = (uint32_t*) malloc (sizeof (uint32_t) * 8);
	memcpy(expected_output, input, 32);

    sparkle(expected_output, 4, 32);

    printf("%s\n", "Expected input");
    print(32, input);
    printf("%s\n", "Expected output");
    print(32, expected_output);



    uint8_t* input_hacl = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    uint8_t* output_hacl = (uint8_t*) malloc (sizeof (uint8_t) * 32);

    Hacl_Impl_Sparkle_sparkle256(32, input_hacl, output_hacl);
    printf("%s\n", "Input");
    compare_and_print(32, input, input_hacl);
    printf("%s\n", "Output");
    compare_and_print(32, expected_output, output_hacl);




    for (int j = 0; j < ROUNDS; j++)
        sparkle(expected_output, 4, 32);
    

	cycles a,b;
    clock_t t1,t2;

    t1 = clock();
    a = cpucycles_begin();

    for (int j = 0; j < ROUNDS; j++)
    	sparkle(expected_output, 4, 32);
    
    b = cpucycles_end();
    t2 = clock();
    clock_t tdiff = t2 - t1;

    double timeSparkleOriginal = (((double)tdiff) );
    double nsigsSparkleOriginal = ((double)ROUNDS) / timeSparkleOriginal;
    printf("Sparkle PERF \n");
    printf("Sparkle op/s\n",nsigsSparkleOriginal);

    cycles cdiff = b - a;
    printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff/ROUNDS);



    for (int j = 0; j < ROUNDS; j++)
        Hacl_Impl_Sparkle_sparkle256(32, output_hacl, output_hacl);

	t1 = clock();
    a = cpucycles_begin();

    for (int j = 0; j < ROUNDS; j++)
    	Hacl_Impl_Sparkle_sparkle256(32, output_hacl, output_hacl);
    
    b = cpucycles_end();
    t2 = clock();
    tdiff = t2 - t1;

    timeSparkleOriginal = (((double)tdiff));
    nsigsSparkleOriginal = ((double)ROUNDS) / timeSparkleOriginal;
    printf("Sparkle PERF \n");
    printf("Sparkle op/s\n",nsigsSparkleOriginal);
	
	cdiff = b - a;
    printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff/ROUNDS);

	return 0;
}