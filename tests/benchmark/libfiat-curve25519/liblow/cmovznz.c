#include <stdint.h>
#include "liblow.h"
uint64_t cmovznz(uint64_t t, uint64_t z, uint64_t nz) {
  asm ("testq %1, %1;" "\n"
  "\t" "cmovnzq %3, %0;"
      :"=r"(z)
      :"r"(t), "0"(z), "r"(nz)
      );
  return z;
}
uint64_t cmovznz64(uint64_t t, uint64_t z, uint64_t nz) {
  return cmovznz(t, z, nz);
}
