#include <stddef.h>
#include <stdlib.h>

#include "benchmark.h"

void b_init()
{
  srand(0);
}

extern void b_randomize(char *buf, size_t buf_sz)
{
  for (int i = 0; i < buf_sz; i++)
    buf[i] = rand() % 8;
}