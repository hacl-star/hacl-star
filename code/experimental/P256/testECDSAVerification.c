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


#include "ecdsap256-c/Hacl_Impl_ECDSA_P256SHA256_Verification.h"

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

void printfb(bool result)
{
  if (result == 0)
    printf("%s\n", "false");
  else if (result == 1)
    printf("%s\n", "true");
  else
    printf("%s\n", "magic");  
}

void test1()
   {
      uint8_t* m = (uint8_t *) malloc (sizeof (uint8_t) * 128);
     m[0] = 0xe1;
m[1] = 0x13;
m[2] = 0x0a;
m[3] = 0xf6;
m[4] = 0xa3;
m[5] = 0x8c;
m[6] = 0xcb;
m[7] = 0x41;
m[8] = 0x2a;
m[9] = 0x9c;
m[10] = 0x8d;
m[11] = 0x13;
m[12] = 0xe1;
m[13] = 0x5d;
m[14] = 0xbf;
m[15] = 0xc9;
m[16] = 0xe6;
m[17] = 0x9a;
m[18] = 0x16;
m[19] = 0x38;
m[20] = 0x5a;
m[21] = 0xf3;
m[22] = 0xc3;
m[23] = 0xf1;
m[24] = 0xe5;
m[25] = 0xda;
m[26] = 0x95;
m[27] = 0x4f;
m[28] = 0xd5;
m[29] = 0xe7;
m[30] = 0xc4;
m[31] = 0x5f;
m[32] = 0xd7;
m[33] = 0x5e;
m[34] = 0x2b;
m[35] = 0x8c;
m[36] = 0x36;
m[37] = 0x69;
m[38] = 0x92;
m[39] = 0x28;
m[40] = 0xe9;
m[41] = 0x28;
m[42] = 0x40;
m[43] = 0xc0;
m[44] = 0x56;
m[45] = 0x2f;
m[46] = 0xbf;
m[47] = 0x37;
m[48] = 0x72;
m[49] = 0xf0;
m[50] = 0x7e;
m[51] = 0x17;
m[52] = 0xf1;
m[53] = 0xad;
m[54] = 0xd5;
m[55] = 0x65;
m[56] = 0x88;
m[57] = 0xdd;
m[58] = 0x45;
m[59] = 0xf7;
m[60] = 0x45;
m[61] = 0x0e;
m[62] = 0x12;
m[63] = 0x17;
m[64] = 0xad;
m[65] = 0x23;
m[66] = 0x99;
m[67] = 0x22;
m[68] = 0xdd;
m[69] = 0x9c;
m[70] = 0x32;
m[71] = 0x69;
m[72] = 0x5d;
m[73] = 0xc7;
m[74] = 0x1f;
m[75] = 0xf2;
m[76] = 0x42;
m[77] = 0x4c;
m[78] = 0xa0;
m[79] = 0xde;
m[80] = 0xc1;
m[81] = 0x32;
m[82] = 0x1a;
m[83] = 0xa4;
m[84] = 0x70;
m[85] = 0x64;
m[86] = 0xa0;
m[87] = 0x44;
m[88] = 0xb7;
m[89] = 0xfe;
m[90] = 0x3c;
m[91] = 0x2b;
m[92] = 0x97;
m[93] = 0xd0;
m[94] = 0x3c;
m[95] = 0xe4;
m[96] = 0x70;
m[97] = 0xa5;
m[98] = 0x92;
m[99] = 0x30;
m[100] = 0x4c;
m[101] = 0x5e;
m[102] = 0xf2;
m[103] = 0x1e;
m[104] = 0xed;
m[105] = 0x9f;
m[106] = 0x93;
m[107] = 0xda;
m[108] = 0x56;
m[109] = 0xbb;
m[110] = 0x23;
m[111] = 0x2d;
m[112] = 0x1e;
m[113] = 0xeb;
m[114] = 0x00;
m[115] = 0x35;
m[116] = 0xf9;
m[117] = 0xbf;
m[118] = 0x0d;
m[119] = 0xfa;
m[120] = 0xfd;
m[121] = 0xcc;
m[122] = 0x46;
m[123] = 0x06;
m[124] = 0x27;
m[125] = 0x2b;
m[126] = 0x20;
m[127] = 0xa3;


      uint32_t mLen = 128;
      uint64_t* pubKey = (uint64_t *) malloc (sizeof (uint64_t) * 12);
      uint64_t* r = (uint64_t *) malloc (sizeof (uint64_t) * 4);
      uint64_t* s = (uint64_t *) malloc (sizeof (uint64_t) * 4);
      
      pubKey[3] = 0xe424dc61d4bb3cb7ul;
      pubKey[2] = 0xef4344a7f8957a0cul;
      pubKey[1] = 0x5134e16f7a67c074ul;
      pubKey[0] = 0xf82e6e12f49abf3cul;

      pubKey[7] = 0x970eed7aa2bc4865ul;
      pubKey[6] = 0x1545949de1dddaf0ul;
      pubKey[5] = 0x127e5965ac85d124ul;
      pubKey[4] = 0x3d6f60e7dfaee927ul;

      r[3] =  0xbf96b99aa49c705cul;
      r[2] =  0x910be33142017c64ul;
      r[1] =  0x2ff540c76349b9daul;
      r[0] =  0xb72f981fd9347f4ful;
 
      s[3] =  0x17c55095819089c2ul;
      s[2] =  0xe03b9cd415abdf12ul;
      s[1] =  0x444e323075d98f31ul;
      s[0] =  0x920b9e0f57ec871cul;

      bool result = Hacl_Impl_ECDSA_P256SHA256_Verification_ecdsa_verification (pubKey, r, s, mLen, m);
      printfb(result);


   }

int main()
{
   test1();

}