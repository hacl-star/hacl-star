#include "stdio.h"
#include "stdlib.h"
#include <fcntl.h>
#include <unistd.h>
#include <inttypes.h>
#include "hacl_test_utils.h"

void randombytes(uint8_t * x,uint64_t len) {
  if (! (read_random_bytes(len, x)))
    exit(1);
}
