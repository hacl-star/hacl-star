#include <stdio.h>

extern void gimli(unsigned int *);

int main()
{
  unsigned int x[12];
  int i;

  for (i = 0;i < 12;++i) x[i] = i * i * i + i * 0x9e3779b9;

  for (i = 0;i < 12;++i) {
    printf("%08x ",x[i]);
    if (i % 4 == 3) printf("\n");
  }
  printf("----------------------\n");

  gimli(x);

  for (i = 0;i < 12;++i) {
    printf("%08x ",x[i]);
    if (i % 4 == 3) printf("\n");
  }
  printf("----------------------\n");
  return 0;
}
