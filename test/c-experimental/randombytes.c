#include "stdio.h"
#include "stdlib.h"
#include <fcntl.h>
#include <unistd.h>
#include <inttypes.h>

void randombytes(uint8_t * x,uint64_t len) {
  int fd = open("/dev/urandom", O_RDONLY);
  uint64_t res = read(fd, x, len);
  if (res != len) {
    printf("Error on reading, got %" PRIu64 " bytes\n", res);
    exit(1);
  }
}
