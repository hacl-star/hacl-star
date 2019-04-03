#include <stdlib.h>

extern int
randombytes(unsigned char *x, unsigned long long xlen);

void randombytes_init_(unsigned char *entropy_input) {
  return;
}

void randombytes_(unsigned long long xlen, unsigned char *x) {
  randombytes(x, xlen);
}
