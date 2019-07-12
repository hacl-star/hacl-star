#include <stdlib.h>

extern void
randombytes_init(unsigned char *entropy_input,
                 unsigned char *personalization_string,
                 int security_strength);

extern int
randombytes(unsigned char *x, unsigned long long xlen);


void randombytes_init_(unsigned char *entropy_input) {
  randombytes_init(entropy_input, NULL, 256);
}

void randombytes_(unsigned long long xlen, unsigned char *x) {
  randombytes(x, xlen);
}
