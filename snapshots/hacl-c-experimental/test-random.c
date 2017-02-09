#include "kremlib.h"
#include "testlib.h"
#include "Random.h"


int32_t main()
{

  uint32_t r32 = random_uint32();
  uint64_t r64 = random_uint64();

  uint8_t r1024[1024];
  random_bytes(r1024, 1024);

  printf("Random (4 Bytes) = ");
  print_bytes((uint8_t*)&r32, 4);

  printf("\nRandom (8 Bytes) = ");
  print_bytes((uint8_t*)&r64, 8);
  
  printf("\nRandom (1024 Bytes) = ");
  print_bytes(r1024, 1024);
  
  return exit_success;
}
