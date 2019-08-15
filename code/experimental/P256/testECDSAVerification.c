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

      bool expectedResult = true;
      if (result == expectedResult)
        printf("%s\n", "Test0: passed");
      else
        printf("%s\n", "Test0: failed");
}


void test2()
   {
      uint8_t* m = (uint8_t *) malloc (sizeof (uint8_t) * 128);
      m[0] = 0xe4;
      m[1] = 0x79;
      m[2] = 0x6d;
      m[3] = 0xb5;
      m[4] = 0xf7;
      m[5] = 0x85;
      m[6] = 0xf2;
      m[7] = 0x07;
      m[8] = 0xaa;
      m[9] = 0x30;
      m[10] = 0xd3;
      m[11] = 0x11;
      m[12] = 0x69;
      m[13] = 0x3b;
      m[14] = 0x37;
      m[15] = 0x02;
      m[16] = 0x82;
      m[17] = 0x1d;
      m[18] = 0xff;
      m[19] = 0x11;
      m[20] = 0x68;
      m[21] = 0xfd;
      m[22] = 0x2e;
      m[23] = 0x04;
      m[24] = 0xc0;
      m[25] = 0x83;
      m[26] = 0x68;
      m[27] = 0x25;
      m[28] = 0xae;
      m[29] = 0xfd;
      m[30] = 0x85;
      m[31] = 0x0d;
      m[32] = 0x9a;
      m[33] = 0xa6;
      m[34] = 0x03;
      m[35] = 0x26;
      m[36] = 0xd8;
      m[37] = 0x8c;
      m[38] = 0xde;
      m[39] = 0x1a;
      m[40] = 0x23;
      m[41] = 0xc7;
      m[42] = 0x74;
      m[43] = 0x53;
      m[44] = 0x51;
      m[45] = 0x39;
      m[46] = 0x2c;
      m[47] = 0xa2;
      m[48] = 0x28;
      m[49] = 0x8d;
      m[50] = 0x63;
      m[51] = 0x2c;
      m[52] = 0x26;
      m[53] = 0x4f;
      m[54] = 0x19;
      m[55] = 0x7d;
      m[56] = 0x05;
      m[57] = 0xcd;
      m[58] = 0x42;
      m[59] = 0x4a;
      m[60] = 0x30;
      m[61] = 0x33;
      m[62] = 0x6c;
      m[63] = 0x19;
      m[64] = 0xfd;
      m[65] = 0x09;
      m[66] = 0xbb;
      m[67] = 0x22;
      m[68] = 0x96;
      m[69] = 0x54;
      m[70] = 0xf0;
      m[71] = 0x22;
      m[72] = 0x2f;
      m[73] = 0xcb;
      m[74] = 0x88;
      m[75] = 0x1a;
      m[76] = 0x4b;
      m[77] = 0x35;
      m[78] = 0xc2;
      m[79] = 0x90;
      m[80] = 0xa0;
      m[81] = 0x93;
      m[82] = 0xac;
      m[83] = 0x15;
      m[84] = 0x9c;
      m[85] = 0xe1;
      m[86] = 0x34;
      m[87] = 0x09;
      m[88] = 0x11;
      m[89] = 0x1f;
      m[90] = 0xf0;
      m[91] = 0x35;
      m[92] = 0x84;
      m[93] = 0x11;
      m[94] = 0x13;
      m[95] = 0x3c;
      m[96] = 0x24;
      m[97] = 0xf5;
      m[98] = 0xb8;
      m[99] = 0xe2;
      m[100] = 0x09;
      m[101] = 0x0d;
      m[102] = 0x6d;
      m[103] = 0xb6;
      m[104] = 0x55;
      m[105] = 0x8a;
      m[106] = 0xfc;
      m[107] = 0x36;
      m[108] = 0xf0;
      m[109] = 0x6c;
      m[110] = 0xa1;
      m[111] = 0xf6;
      m[112] = 0xef;
      m[113] = 0x77;
      m[114] = 0x97;
      m[115] = 0x85;
      m[116] = 0xad;
      m[117] = 0xba;
      m[118] = 0x68;
      m[119] = 0xdb;
      m[120] = 0x27;
      m[121] = 0xa4;
      m[122] = 0x09;
      m[123] = 0x85;
      m[124] = 0x9f;
      m[125] = 0xc4;
      m[126] = 0xc4;
      m[127] = 0xa0;


      uint32_t mLen = 128;
      uint64_t* pubKey = (uint64_t *) malloc (sizeof (uint64_t) * 12);
      uint64_t* r = (uint64_t *) malloc (sizeof (uint64_t) * 4);
      uint64_t* s = (uint64_t *) malloc (sizeof (uint64_t) * 4);
      
      pubKey[3] = 0x87f8f2b218f49845ul;
      pubKey[2] = 0xf6f10eec38771362ul;
      pubKey[1] = 0x69f5c1a54736dbdful;
      pubKey[0] = 0x69f89940cad41555ul;

      pubKey[7] = 0xe15f369036f49842;
      pubKey[6] = 0xfac7a86c8a2b0557;
      pubKey[5] = 0x609776814448b8f5;
      pubKey[4] = 0xe84aa9f4395205e9;

      r[3] =  0xd19ff48b32491557;
      r[2] =  0x6416097d2544f7cb;
      r[1] =  0xdf8768b1454ad20e;
      r[0] =  0x0baac50e211f23b0;
 
      s[3] =  0xa3e81e59311cdfff;
      s[2] =  0x2d4784949f7a2cb5;
      s[1] =  0x0ba6c3a91fa54710;
      s[0] =  0x568e61aca3e847c6;

      bool result = Hacl_Impl_ECDSA_P256SHA256_Verification_ecdsa_verification (pubKey, r, s, mLen, m);

      bool expectedResult = false;
      if (result == expectedResult)
        printf("%s\n", "Test1: passed");
      else
        printf("%s\n", "Test1: failed");
}

void test3()
   {
      uint8_t* m = (uint8_t *) malloc (sizeof (uint8_t) * 128);
      m[0] = 0x73;
      m[1] = 0xc5;
      m[2] = 0xf6;
      m[3] = 0xa6;
      m[4] = 0x74;
      m[5] = 0x56;
      m[6] = 0xae;
      m[7] = 0x48;
      m[8] = 0x20;
      m[9] = 0x9b;
      m[10] = 0x5f;
      m[11] = 0x85;
      m[12] = 0xd1;
      m[13] = 0xe7;
      m[14] = 0xde;
      m[15] = 0x77;
      m[16] = 0x58;
      m[17] = 0xbf;
      m[18] = 0x23;
      m[19] = 0x53;
      m[20] = 0x00;
      m[21] = 0xc6;
      m[22] = 0xae;
      m[23] = 0x2b;
      m[24] = 0xdc;
      m[25] = 0xeb;
      m[26] = 0x1d;
      m[27] = 0xcb;
      m[28] = 0x27;
      m[29] = 0xa7;
      m[30] = 0x73;
      m[31] = 0x0f;
      m[32] = 0xb6;
      m[33] = 0x8c;
      m[34] = 0x95;
      m[35] = 0x0b;
      m[36] = 0x7f;
      m[37] = 0xca;
      m[38] = 0xda;
      m[39] = 0x0e;
      m[40] = 0xcc;
      m[41] = 0x46;
      m[42] = 0x61;
      m[43] = 0xd3;
      m[44] = 0x57;
      m[45] = 0x82;
      m[46] = 0x30;
      m[47] = 0xf2;
      m[48] = 0x25;
      m[49] = 0xa8;
      m[50] = 0x75;
      m[51] = 0xe6;
      m[52] = 0x9a;
      m[53] = 0xaa;
      m[54] = 0x17;
      m[55] = 0xf1;
      m[56] = 0xe7;
      m[57] = 0x1c;
      m[58] = 0x6b;
      m[59] = 0xe5;
      m[60] = 0xc8;
      m[61] = 0x31;
      m[62] = 0xf2;
      m[63] = 0x26;
      m[64] = 0x63;
      m[65] = 0xba;
      m[66] = 0xc6;
      m[67] = 0x3d;
      m[68] = 0x0c;
      m[69] = 0x7a;
      m[70] = 0x96;
      m[71] = 0x35;
      m[72] = 0xed;
      m[73] = 0xb0;
      m[74] = 0x04;
      m[75] = 0x3f;
      m[76] = 0xf8;
      m[77] = 0xc6;
      m[78] = 0xf2;
      m[79] = 0x64;
      m[80] = 0x70;
      m[81] = 0xf0;
      m[82] = 0x2a;
      m[83] = 0x7b;
      m[84] = 0xc5;
      m[85] = 0x65;
      m[86] = 0x56;
      m[87] = 0xf1;
      m[88] = 0x43;
      m[89] = 0x7f;
      m[90] = 0x06;
      m[91] = 0xdf;
      m[92] = 0xa2;
      m[93] = 0x7b;
      m[94] = 0x48;
      m[95] = 0x7a;
      m[96] = 0x6c;
      m[97] = 0x42;
      m[98] = 0x90;
      m[99] = 0xd8;
      m[100] = 0xba;
      m[101] = 0xd3;
      m[102] = 0x8d;
      m[103] = 0x48;
      m[104] = 0x79;
      m[105] = 0xb3;
      m[106] = 0x34;
      m[107] = 0xe3;
      m[108] = 0x41;
      m[109] = 0xba;
      m[110] = 0x09;
      m[111] = 0x2d;
      m[112] = 0xde;
      m[113] = 0x4e;
      m[114] = 0x4a;
      m[115] = 0xe6;
      m[116] = 0x94;
      m[117] = 0xa9;
      m[118] = 0xc0;
      m[119] = 0x93;
      m[120] = 0x02;
      m[121] = 0xe2;
      m[122] = 0xdb;
      m[123] = 0xf4;
      m[124] = 0x43;
      m[125] = 0x58;
      m[126] = 0x1c;
      m[127] = 0x08;




      uint32_t mLen = 128;
      uint64_t* pubKey = (uint64_t *) malloc (sizeof (uint64_t) * 12);
      uint64_t* r = (uint64_t *) malloc (sizeof (uint64_t) * 4);
      uint64_t* s = (uint64_t *) malloc (sizeof (uint64_t) * 4);
      
      pubKey[3] = 0xe0fc6a6f50e1c574;
      pubKey[2] = 0x75673ee54e3a57f9;
      pubKey[1] = 0xa49f3328e743bf52;
      pubKey[0] = 0xf335e3eeaa3d2864;

      pubKey[7] = 0x7f59d689c91e4636;
      pubKey[6] = 0x07d9194d99faf316;
      pubKey[5] = 0xe25432870816dde6;
      pubKey[4] = 0x3f5d4b373f12f22a;

      r[3] =  0x1d75830cd36f4c9a;
      r[2] =  0xa181b2c4221e87f1;
      r[1] =  0x76b7f05b7c87824e;
      r[0] =  0x82e396c88315c407;
 
      s[3] =  0xcb2acb01dac96efc;
      s[2] =  0x53a32d4a0d85d0c2;
      s[1] =  0xe48955214783ecf5;
      s[0] =  0x0a4f0414a319c05a;

      bool result = Hacl_Impl_ECDSA_P256SHA256_Verification_ecdsa_verification (pubKey, r, s, mLen, m);

      bool expectedResult = true;
      if (result == expectedResult)
        printf("%s\n", "Test2: passed");
      else
        printf("%s\n", "Test2: failed");
}





int main()
{
   test1();
   test2();
   test3();

}