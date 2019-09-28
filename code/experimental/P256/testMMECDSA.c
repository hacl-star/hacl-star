#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <time.h>


#include "p256-c/Hacl_Impl_MM_Exponent.h"

#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>


typedef __attribute__((aligned(32))) uint8_t POINT[12 * 8];
typedef __attribute__((aligned(32))) uint8_t SCALAR[32];

typedef uint64_t cycles;

static __inline__ cycles cpucycles(void)
{
  uint64_t rax,rdx,aux;
  asm volatile ( "rdtscp\n" : "=a" (rax), "=d" (rdx), "=c" (aux) : : );
  return (rdx << 32) + rax;
}
#define ROUNDS 10000
#define SIZE   1

uint64_t generateRandom()
{
   return (uint64_t) (((uint64_t) rand() << 33) | rand())%18446744073709551615U;
}


void print_u(uint64_t a)
{
   printf("%" PRIu64 " ", a);
   printf("%u ", (uint32_t) a);
   printf("%u\n", (uint32_t) (a >> 32));
}

void print_uu(uint64_t* a)
{
   print_u(a[0]);
   print_u(a[1]);
   print_u(a[2]);
   print_u(a[3]);
   printf("\n");
}


void print_uu_l (uint64_t* a, int len, bool div)
{
   if (div)
   {
      int counter = 0;
      int i = 0;
      for (i = len; i < len; i++)
      {
         printf("%d\n",counter );
         if (counter == 4)
            {
               printf("\n");
               printf("\n");
               counter = 0;
            }
         print_u(a[i]);
         counter = counter +1;      


      }

   }
   else
   {
      int i = 0;
      for (i = 0; i< len; i++)
      {
         printf("%d", i);
         printf("%s", "   " );
         print_u(a[i]);
      }
   }
}


int main()
{
   uint64_t* a = (uint64_t *) malloc (sizeof (uint64_t) * 4);
   a[0] = 101;
   a[1] = 0;
   a[2] = 0;
   a[3] = 0;

   uint64_t* b = (uint64_t *) malloc (sizeof (uint64_t) * 4);
   b[0] = 100;
   b[1] = 0;
   b[2] = 0;
   b[3] = 0;
   
   
   uint64_t* result = (uint64_t *) malloc (sizeof (uint64_t) * 4);
   Hacl_Impl_MM_Exponent_multPower(a, b, result);
   print_uu(result);


}