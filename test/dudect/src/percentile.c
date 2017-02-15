#include <stdlib.h>
#include <stdio.h>
#include <strings.h>
#include <assert.h>
#include "percentile.h"

static int cmp(const int64_t *a, const int64_t *b) { return (int)(*a - *b); }

int64_t percentile(int64_t *a, double which, size_t size) {
  qsort(a, size, sizeof(int64_t), (int (*)(const void *, const void *))cmp);
  size_t array_position = (size_t)((double)size * (double)which);
  assert(array_position >= 0);
  assert(array_position < size);
  //printf("percentile %f is %lld\n", which, a[array_position]);
  return a[array_position];
}

#if 0
int main(int argc, char **argv)
{
  int64_t a[1000];
  int64_t b[1000];
  for (int i = 0; i< 1000; i++) {
    a[i] = i;
    b[i] = i;
  }

  memcpy(b,a,1000*sizeof(a[0]));
  percentile(b, 0.1, 1000);

  memcpy(b,a,1000*sizeof(a[0]));
  percentile(b, 0.9, 1000);

  memcpy(b,a,1000*sizeof(a[0]));
  percentile(b, 0.25, 1000);

  memcpy(b,a,1000*sizeof(a[0]));
  percentile(b, 0.75, 1000);

  memcpy(b,a,1000*sizeof(a[0]));
  percentile(b, 0.99, 1000);

  memcpy(b,a,1000*sizeof(a[0]));
  percentile(b, 0.999, 1000);
}
#endif
