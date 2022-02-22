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

#include "Hacl_Impl_Sparkle1.h"
#include "sparkle_vectors.h"


#include <stdint.h>
#include <string.h>
#include <stdint.h>

#define ROUNDS 10000

static inline void print(size_t len, uint8_t* comp) {
  for (size_t i = 0; i < len; i++)
    printf("%02x",comp[i]);
  printf("\n");
}


int test()
{
    bool ok = true;
    for (int i = 0; i < sizeof(vectors)/sizeof(sparkle_test_vector); i++)
    {
        uint8_t* output_hacl = (uint8_t*) malloc (sizeof (uint8_t) * vectors[i].len);
        Hacl_Impl_Sparkle1_sparkle256(vectors[i].len, vectors[i].input, output_hacl);
        ok = ok & compare_and_print(vectors[i].len, output_hacl, vectors[i].output);
        free(output_hacl);
    }
}

void speed()
{
    uint8_t* output_hacl = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    cycles a,b;
    clock_t t1,t2;
    for (int j = 0; j < ROUNDS; j++)
        Hacl_Impl_Sparkle1_sparkle256(1000, output_hacl, output_hacl);

    t1 = clock();
    a = cpucycles_begin();

    for (int j = 0; j < ROUNDS; j++)
        Hacl_Impl_Sparkle1_sparkle256(1000, output_hacl, output_hacl);
    
    b = cpucycles_end();
    t2 = clock();

    double timeSparkleOriginal = t2 - t1;
    double nsigsSparkleOriginal = ((double)ROUNDS) / timeSparkleOriginal;
    printf("Sparkle PERF \n");
    printf("Sparkle %f op/s\n",nsigsSparkleOriginal);
    
    uint64_t cdiff = b - a;
    printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff/ROUNDS);

    free(output_hacl);
}


int main(int argc, char const *argv[])
{
    test();
    speed();

	return 0;
}