#include <stdlib.h>

#define DOIT(bits,target) \
int main(int argc,char **argv) \
{ \
  target x; \
  int i; \
 \
  x = (target) atoi(argv[1]); \
  for (i = 0;i < bits;++i) { \
    if (x == 0) return 100; \
    x += x + (target) atoi(argv[2]); \
  } \
  if (x != 0) return 100; \
  x -= 1; \
  if (x < 0) return 100; \
 \
  return 0; \
}
