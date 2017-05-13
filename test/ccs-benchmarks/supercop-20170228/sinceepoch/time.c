#include <stdio.h>
#include <time.h>
#include <sys/time.h>

int main(int argc,char **argv)
{
  long long t = time(0);
  printf("%lld\n",t);
  return 0;
}
