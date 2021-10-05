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

	return 0;
}