#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <inttypes.h>

#include "Lib_Memzero0.h"
#include "kremlin/internal/target.h"

/* The F* formalization talks about the number of elements in the array. The C
   implementation wants a number of bytes in the array. KreMLin is aware of this
   and inserts a sizeof multiplication. */
void Lib_Memzero0_memzero(void *dst, uint64_t len) {
  /* This is safe: kremlin checks at run-time (if needed) that all object sizes
     fit within a size_t, so the size we receive has been checked at
     allocation-time, possibly via KRML_CHECK_SIZE, to fit in a size_t. */
  size_t len_ = (size_t) len;

  /* Default implementation for platforms with no particular support. */
  #warning "Your platform does not support any safe implementation of memzero -- consider a pull request!"
  volatile unsigned char *volatile dst_ = (volatile unsigned char *volatile) dst;
  size_t i = 0U;
  while (i < len)
    dst_[i++] = 0U;
}
