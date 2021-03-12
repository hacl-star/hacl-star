#ifndef __Lib_H
#define __Lib_H

#include <stdint.h>
#include <stdbool.h>
#define KRML_CHECK_SIZE(a,b) {}

static inline uint64_t load64_le(const uint8_t* b){
  uint64_t x;
  memcpy(&x, b, 8);
  return x;
}
static inline void store64_le(uint8_t* b,uint64_t o) {
  memcpy(b,&o,8);
}

#endif
