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

#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>

#include "Hacl_Impl_ECDSA.h"

extern uint64_t Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign_nist(
  uint8_t *result,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);


void printfb(bool result)
{
  if (result == 0)
    printf("%s\n", "false");
  else if (result == 1)
    printf("%s\n", "true");
  else
    printf("%s\n", "magic");  
}



void print9(uint8_t* a)
{
  int i = 0;
  for (i = 31; i >= 0; i--)
  {
    printf("%hhX ", a[i]);
  }
  printf("%s\n", "");
}


void testEcdsaSignature0()
{
    uint8_t* m = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* privateKey = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* k = (uint8_t *) malloc (sizeof (uint8_t) * 32);

    uint8_t* result = (uint8_t *) malloc (sizeof (uint8_t) * 64);

    uint8_t* expectedR = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    uint8_t* expectedS = (uint8_t*) malloc (sizeof (uint8_t) * 32);

        m[31] = 0x44;
        m[30] = 0xac;
        m[29] = 0xf6;
        m[28] = 0xb7;
        m[27] = 0xe3;
        m[26] = 0x6c;
        m[25] = 0x13;
        m[24] = 0x42;
        m[23] = 0xc2;
        m[22] = 0xc5;
        m[21] = 0x89;
        m[20] = 0x72;
        m[19] = 0x04;
        m[18] = 0xfe;
        m[17] = 0x09;
        m[16] = 0x50;
        m[15] = 0x4e;
        m[14] = 0x1e;
        m[13] = 0x2e;
        m[12] = 0xfb;
        m[11] = 0x1a;
        m[10] = 0x90;
        m[9] = 0x03;
        m[8] = 0x77;
        m[7] = 0xdb;
        m[6] = 0xc4;
        m[5] = 0xe7;
        m[4] = 0xa6;
        m[3] = 0xa1;
        m[2] = 0x33;
        m[1] = 0xec;
        m[0] = 0x56;
        
        privateKey[31] = 0x51;
        privateKey[30] = 0x9b;
        privateKey[29] = 0x42;
        privateKey[28] = 0x3d;
        privateKey[27] = 0x71;
        privateKey[26] = 0x5f;
        privateKey[25] = 0x8b;
        privateKey[24] = 0x58;
        privateKey[23] = 0x1f;
        privateKey[22] = 0x4f;
        privateKey[21] = 0xa8;
        privateKey[20] = 0xee;
        privateKey[19] = 0x59;
        privateKey[18] = 0xf4;
        privateKey[17] = 0x77;
        privateKey[16] = 0x1a;
        privateKey[15] = 0x5b;
        privateKey[14] = 0x44;
        privateKey[13] = 0xc8;
        privateKey[12] = 0x13;
        privateKey[11] = 0x0b;
        privateKey[10] = 0x4e;
        privateKey[9] = 0x3e;
        privateKey[8] = 0xac;
        privateKey[7] = 0xca;
        privateKey[6] = 0x54;
        privateKey[5] = 0xa5;
        privateKey[4] = 0x6d;
        privateKey[3] = 0xda;
        privateKey[2] = 0x72;
        privateKey[1] = 0xb4;
        privateKey[0] = 0x64;
    

        k[31] = 0x94;
        k[30] = 0xa1;
        k[29] = 0xbb;
        k[28] = 0xb1;
        k[27] = 0x4b;
        k[26] = 0x90;
        k[25] = 0x6a;
        k[24] = 0x61;
        k[23] = 0xa2;
        k[22] = 0x80;
        k[21] = 0xf2;
        k[20] = 0x45;
        k[19] = 0xf9;
        k[18] = 0xe9;
        k[17] = 0x3c;
        k[16] = 0x7f;
        k[15] = 0x3b;
        k[14] = 0x4a;
        k[13] = 0x62;
        k[12] = 0x47;
        k[11] = 0x82;
        k[10] = 0x4f;
        k[9] = 0x5d;
        k[8] = 0x33;
        k[7] = 0xb9;
        k[6] = 0x67;
        k[5] = 0x07;
        k[4] = 0x87;
        k[3] = 0x64;
        k[2] = 0x2a;
        k[1] = 0x68;
        k[0] = 0xde;
    
       
        expectedR[31] = 0xf3;
        expectedR[30] = 0xac;
        expectedR[29] = 0x80;
        expectedR[28] = 0x61;
        expectedR[27] = 0xb5;
        expectedR[26] = 0x14;
        expectedR[25] = 0x79;
        expectedR[24] = 0x5b;
        expectedR[23] = 0x88;
        expectedR[22] = 0x43;
        expectedR[21] = 0xe3;
        expectedR[20] = 0xd6;
        expectedR[19] = 0x62;
        expectedR[18] = 0x95;
        expectedR[17] = 0x27;
        expectedR[16] = 0xed;
        expectedR[15] = 0x2a;
        expectedR[14] = 0xfd;
        expectedR[13] = 0x6b;
        expectedR[12] = 0x1f;
        expectedR[11] = 0x6a;
        expectedR[10] = 0x55;
        expectedR[9] = 0x5a;
        expectedR[8] = 0x7a;
        expectedR[7] = 0xca;
        expectedR[6] = 0xbb;
        expectedR[5] = 0x5e;
        expectedR[4] = 0x6f;
        expectedR[3] = 0x79;
        expectedR[2] = 0xc8;
        expectedR[1] = 0xc2;
        expectedR[0] = 0xac;

        expectedS[31] = 0x8b;
        expectedS[30] = 0xf7;
        expectedS[29] = 0x78;
        expectedS[28] = 0x19;
        expectedS[27] = 0xca;
        expectedS[26] = 0x05;
        expectedS[25] = 0xa6;
        expectedS[24] = 0xb2;
        expectedS[23] = 0x78;
        expectedS[22] = 0x6c;
        expectedS[21] = 0x76;
        expectedS[20] = 0x26;
        expectedS[19] = 0x2b;
        expectedS[18] = 0xf7;
        expectedS[17] = 0x37;
        expectedS[16] = 0x1c;
        expectedS[15] = 0xef;
        expectedS[14] = 0x97;
        expectedS[13] = 0xb2;
        expectedS[12] = 0x18;
        expectedS[11] = 0xe9;
        expectedS[10] = 0x6f;
        expectedS[9] = 0x17;
        expectedS[8] = 0x5a;
        expectedS[7] = 0x3c;
        expectedS[6] = 0xcd;
        expectedS[5] = 0xda;
        expectedS[4] = 0x2a;
        expectedS[3] = 0xcc;
        expectedS[2] = 0x05;
        expectedS[1] = 0x89;
        expectedS[0] = 0x03;
          

    uint64_t flag = Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign_nist(result, m, privateKey, k);
    
    bool flagCorrectR = true;
    for (int i = 0; i < 32; i++)
        flagCorrectR = flagCorrectR && (result[i] == expectedR[i]);

    bool flagCorrectS = true;
    for (int i = 0; i < 32; i++)
        flagCorrectS = flagCorrectS && (result[i + 32] == expectedS[i]);


    uint64_t expectedResult = 0x0;
      if (flag == expectedResult && flagCorrectR && flagCorrectS)
        printf("%s\n", "Test0: passed");
      else
        printf("%s\n", "Test0: failed");

}

void testEcdsaSignature1()
{    
    uint8_t* m = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* privateKey = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* k = (uint8_t *) malloc (sizeof (uint8_t) * 32);

    uint8_t* result = (uint8_t *) malloc (sizeof (uint8_t) * 64);

    uint8_t* expectedR = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    uint8_t* expectedS = (uint8_t*) malloc (sizeof (uint8_t) * 32);



        m[31] = 0x9b;
        m[30] = 0x2d;
        m[29] = 0xb8;
        m[28] = 0x9c;
        m[27] = 0xb0;
        m[26] = 0xe8;
        m[25] = 0xfa;
        m[24] = 0x3c;
        m[23] = 0xc7;
        m[22] = 0x60;
        m[21] = 0x8b;
        m[20] = 0x4d;
        m[19] = 0x6c;
        m[18] = 0xc1;
        m[17] = 0xde;
        m[16] = 0xc0;
        m[15] = 0x11;
        m[14] = 0x4e;
        m[13] = 0x0b;
        m[12] = 0x9f;
        m[11] = 0xf4;
        m[10] = 0x08;
        m[9] = 0x0b;
        m[8] = 0xea;
        m[7] = 0x12;
        m[6] = 0xb1;
        m[5] = 0x34;
        m[4] = 0xf4;
        m[3] = 0x89;
        m[2] = 0xab;
        m[1] = 0x2b;
        m[0] = 0xbc;

        privateKey[31] = 0x0f;
        privateKey[30] = 0x56;
        privateKey[29] = 0xdb;
        privateKey[28] = 0x78;
        privateKey[27] = 0xca;
        privateKey[26] = 0x46;
        privateKey[25] = 0x0b;
        privateKey[24] = 0x05;
        privateKey[23] = 0x5c;
        privateKey[22] = 0x50;
        privateKey[21] = 0x00;
        privateKey[20] = 0x64;
        privateKey[19] = 0x82;
        privateKey[18] = 0x4b;
        privateKey[17] = 0xed;
        privateKey[16] = 0x99;
        privateKey[15] = 0x9a;
        privateKey[14] = 0x25;
        privateKey[13] = 0xaa;
        privateKey[12] = 0xf4;
        privateKey[11] = 0x8e;
        privateKey[10] = 0xbb;
        privateKey[9] = 0x51;
        privateKey[8] = 0x9a;
        privateKey[7] = 0xc2;
        privateKey[6] = 0x01;
        privateKey[5] = 0x53;
        privateKey[4] = 0x7b;
        privateKey[3] = 0x85;
        privateKey[2] = 0x47;
        privateKey[1] = 0x98;
        privateKey[0] = 0x13;

        k[31] = 0x6d;
        k[30] = 0x3e;
        k[29] = 0x71;
        k[28] = 0x88;
        k[27] = 0x2c;
        k[26] = 0x3b;
        k[25] = 0x83;
        k[24] = 0xb1;
        k[23] = 0x56;
        k[22] = 0xbb;
        k[21] = 0x14;
        k[20] = 0xe0;
        k[19] = 0xab;
        k[18] = 0x18;
        k[17] = 0x4a;
        k[16] = 0xa9;
        k[15] = 0xfb;
        k[14] = 0x72;
        k[13] = 0x80;
        k[12] = 0x68;
        k[11] = 0xd3;
        k[10] = 0xae;
        k[9] = 0x9f;
        k[8] = 0xac;
        k[7] = 0x42;
        k[6] = 0x11;
        k[5] = 0x87;
        k[4] = 0xae;
        k[3] = 0x0b;
        k[2] = 0x2f;
        k[1] = 0x34;
        k[0] = 0xc6;

        expectedR[31] = 0x97;
        expectedR[30] = 0x6d;
        expectedR[29] = 0x3a;
        expectedR[28] = 0x4e;
        expectedR[27] = 0x9d;
        expectedR[26] = 0x23;
        expectedR[25] = 0x32;
        expectedR[24] = 0x6d;
        expectedR[23] = 0xc0;
        expectedR[22] = 0xba;
        expectedR[21] = 0xa9;
        expectedR[20] = 0xfa;
        expectedR[19] = 0x56;
        expectedR[18] = 0x0b;
        expectedR[17] = 0x7c;
        expectedR[16] = 0x4e;
        expectedR[15] = 0x53;
        expectedR[14] = 0xf4;
        expectedR[13] = 0x28;
        expectedR[12] = 0x64;
        expectedR[11] = 0xf5;
        expectedR[10] = 0x08;
        expectedR[9] = 0x48;
        expectedR[8] = 0x3a;
        expectedR[7] = 0x64;
        expectedR[6] = 0x73;
        expectedR[5] = 0xb6;
        expectedR[4] = 0xa1;
        expectedR[3] = 0x10;
        expectedR[2] = 0x79;
        expectedR[1] = 0xb2;
        expectedR[0] = 0xdb;

        expectedS[31] = 0x1b;
        expectedS[30] = 0x76;
        expectedS[29] = 0x6e;
        expectedS[28] = 0x9c;
        expectedS[27] = 0xeb;
        expectedS[26] = 0x71;
        expectedS[25] = 0xba;
        expectedS[24] = 0x6c;
        expectedS[23] = 0x01;
        expectedS[22] = 0xdc;
        expectedS[21] = 0xd4;
        expectedS[20] = 0x6e;
        expectedS[19] = 0x0a;
        expectedS[18] = 0xf4;
        expectedS[17] = 0x62;
        expectedS[16] = 0xcd;
        expectedS[15] = 0x4c;
        expectedS[14] = 0xfa;
        expectedS[13] = 0x65;
        expectedS[12] = 0x2a;
        expectedS[11] = 0xe5;
        expectedS[10] = 0x01;
        expectedS[9] = 0x7d;
        expectedS[8] = 0x45;
        expectedS[7] = 0x55;
        expectedS[6] = 0xb8;
        expectedS[5] = 0xee;
        expectedS[4] = 0xef;
        expectedS[3] = 0xe3;
        expectedS[2] = 0x6e;
        expectedS[1] = 0x19;
        expectedS[0] = 0x32;


    uint64_t flag = Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign_nist(result, m, privateKey, k);
    
    bool flagCorrectR = true;
    for (int i = 0; i < 32; i++)
        flagCorrectR = flagCorrectR && (result[i] == expectedR[i]);

    bool flagCorrectS = true;
    for (int i = 0; i < 32; i++)
        flagCorrectS = flagCorrectS && (result[i + 32] == expectedS[i]);


    uint64_t expectedResult = 0x0;
      if (flag == expectedResult && flagCorrectR && flagCorrectS)
        printf("%s\n", "Test1: passed");
      else
        printf("%s\n", "Test1: failed");

}


void testEcdsaSignature2()
{    
    uint8_t* m = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* privateKey = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* k = (uint8_t *) malloc (sizeof (uint8_t) * 32);

    uint8_t* result = (uint8_t *) malloc (sizeof (uint8_t) * 64);

    uint8_t* expectedR = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    uint8_t* expectedS = (uint8_t*) malloc (sizeof (uint8_t) * 32);

        m[31] = 0xb8;
        m[30] = 0x04;
        m[29] = 0xcf;
        m[28] = 0x88;
        m[27] = 0xaf;
        m[26] = 0x0c;
        m[25] = 0x2e;
        m[24] = 0xff;
        m[23] = 0x8b;
        m[22] = 0xbb;
        m[21] = 0xfb;
        m[20] = 0x36;
        m[19] = 0x60;
        m[18] = 0xeb;
        m[17] = 0xb3;
        m[16] = 0x29;
        m[15] = 0x41;
        m[14] = 0x38;
        m[13] = 0xe9;
        m[12] = 0xd3;
        m[11] = 0xeb;
        m[10] = 0xd4;
        m[9] = 0x58;
        m[8] = 0x88;
        m[7] = 0x4e;
        m[6] = 0x19;
        m[5] = 0x81;
        m[4] = 0x80;
        m[3] = 0x61;
        m[2] = 0xda;
        m[1] = 0xcf;
        m[0] = 0xf0;

        privateKey[31] = 0xe2;
        privateKey[30] = 0x83;
        privateKey[29] = 0x87;
        privateKey[28] = 0x12;
        privateKey[27] = 0x39;
        privateKey[26] = 0x83;
        privateKey[25] = 0x7e;
        privateKey[24] = 0x13;
        privateKey[23] = 0xb9;
        privateKey[22] = 0x5f;
        privateKey[21] = 0x78;
        privateKey[20] = 0x9e;
        privateKey[19] = 0x6e;
        privateKey[18] = 0x1a;
        privateKey[17] = 0xf6;
        privateKey[16] = 0x3b;
        privateKey[15] = 0xf6;
        privateKey[14] = 0x1c;
        privateKey[13] = 0x91;
        privateKey[12] = 0x8c;
        privateKey[11] = 0x99;
        privateKey[10] = 0x2e;
        privateKey[9] = 0x62;
        privateKey[8] = 0xbc;
        privateKey[7] = 0xa0;
        privateKey[6] = 0x40;
        privateKey[5] = 0xd6;
        privateKey[4] = 0x4c;
        privateKey[3] = 0xad;
        privateKey[2] = 0x1f;
        privateKey[1] = 0xc2;
        privateKey[0] = 0xef;

        k[31] = 0xad;
        k[30] = 0x5e;
        k[29] = 0x88;
        k[28] = 0x7e;
        k[27] = 0xb2;
        k[26] = 0xb3;
        k[25] = 0x80;
        k[24] = 0xb8;
        k[23] = 0xd8;
        k[22] = 0x28;
        k[21] = 0x0a;
        k[20] = 0xd6;
        k[19] = 0xe5;
        k[18] = 0xff;
        k[17] = 0x8a;
        k[16] = 0x60;
        k[15] = 0xf4;
        k[14] = 0xd2;
        k[13] = 0x62;
        k[12] = 0x43;
        k[11] = 0xe0;
        k[10] = 0x12;
        k[9] = 0x4c;
        k[8] = 0x2f;
        k[7] = 0x31;
        k[6] = 0xa2;
        k[5] = 0x97;
        k[4] = 0xb5;
        k[3] = 0xd0;
        k[2] = 0x83;
        k[1] = 0x5d;
        k[0] = 0xe2;

        expectedR[31] = 0x35;
        expectedR[30] = 0xfb;
        expectedR[29] = 0x60;
        expectedR[28] = 0xf5;
        expectedR[27] = 0xca;
        expectedR[26] = 0x0f;
        expectedR[25] = 0x3c;
        expectedR[24] = 0xa0;
        expectedR[23] = 0x85;
        expectedR[22] = 0x42;
        expectedR[21] = 0xfb;
        expectedR[20] = 0x3c;
        expectedR[19] = 0xc6;
        expectedR[18] = 0x41;
        expectedR[17] = 0xc8;
        expectedR[16] = 0x26;
        expectedR[15] = 0x3a;
        expectedR[14] = 0x2c;
        expectedR[13] = 0xab;
        expectedR[12] = 0x7a;
        expectedR[11] = 0x90;
        expectedR[10] = 0xee;
        expectedR[9] = 0x6a;
        expectedR[8] = 0x5e;
        expectedR[7] = 0x15;
        expectedR[6] = 0x83;
        expectedR[5] = 0xfa;
        expectedR[4] = 0xc2;
        expectedR[3] = 0xbb;
        expectedR[2] = 0x6f;
        expectedR[1] = 0x6b;
        expectedR[0] = 0xd1;

        expectedS[31] = 0xee;
        expectedS[30] = 0x59;
        expectedS[29] = 0xd8;
        expectedS[28] = 0x1b;
        expectedS[27] = 0xc9;
        expectedS[26] = 0xdb;
        expectedS[25] = 0x10;
        expectedS[24] = 0x55;
        expectedS[23] = 0xcc;
        expectedS[22] = 0x0e;
        expectedS[21] = 0xd9;
        expectedS[20] = 0x7b;
        expectedS[19] = 0x15;
        expectedS[18] = 0x9d;
        expectedS[17] = 0x87;
        expectedS[16] = 0x84;
        expectedS[15] = 0xaf;
        expectedS[14] = 0x04;
        expectedS[13] = 0xe9;
        expectedS[12] = 0x85;
        expectedS[11] = 0x11;
        expectedS[10] = 0xd0;
        expectedS[9] = 0xa9;
        expectedS[8] = 0xa4;
        expectedS[7] = 0x07;
        expectedS[6] = 0xb9;
        expectedS[5] = 0x9b;
        expectedS[4] = 0xb2;
        expectedS[3] = 0x92;
        expectedS[2] = 0x57;
        expectedS[1] = 0x2e;
        expectedS[0] = 0x96;


    uint64_t flag = Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign_nist(result, m, privateKey, k);
    
    bool flagCorrectR = true;
    for (int i = 0; i < 32; i++)
        flagCorrectR = flagCorrectR && (result[i] == expectedR[i]);

    bool flagCorrectS = true;
    for (int i = 0; i < 32; i++)
        flagCorrectS = flagCorrectS && (result[i + 32] == expectedS[i]);


    uint64_t expectedResult = 0x0;
      if (flag == expectedResult && flagCorrectR && flagCorrectS)
        printf("%s\n", "Test2: passed");
      else
        printf("%s\n", "Test2: failed");

}

void testEcdsaSignature3()
{    
    uint8_t* m = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* privateKey = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* k = (uint8_t *) malloc (sizeof (uint8_t) * 32);

    uint8_t* result = (uint8_t *) malloc (sizeof (uint8_t) * 64);

    uint8_t* expectedR = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    uint8_t* expectedS = (uint8_t*) malloc (sizeof (uint8_t) * 32);

        m[31] = 0x85;
        m[30] = 0xb9;
        m[29] = 0x57;
        m[28] = 0xd9;
        m[27] = 0x27;
        m[26] = 0x66;
        m[25] = 0x23;
        m[24] = 0x5e;
        m[23] = 0x7c;
        m[22] = 0x88;
        m[21] = 0x0a;
        m[20] = 0xc5;
        m[19] = 0x44;
        m[18] = 0x7c;
        m[17] = 0xfb;
        m[16] = 0xe9;
        m[15] = 0x7f;
        m[14] = 0x3c;
        m[13] = 0xb4;
        m[12] = 0x99;
        m[11] = 0xf4;
        m[10] = 0x86;
        m[9] = 0xd1;
        m[8] = 0xe4;
        m[7] = 0x3b;
        m[6] = 0xcb;
        m[5] = 0x5c;
        m[4] = 0x2f;
        m[3] = 0xf9;
        m[2] = 0x60;
        m[1] = 0x8a;
        m[0] = 0x1a;
        privateKey[31] = 0xa3;
        privateKey[30] = 0xd2;
        privateKey[29] = 0xd3;
        privateKey[28] = 0xb7;
        privateKey[27] = 0x59;
        privateKey[26] = 0x6f;
        privateKey[25] = 0x65;
        privateKey[24] = 0x92;
        privateKey[23] = 0xce;
        privateKey[22] = 0x98;
        privateKey[21] = 0xb4;
        privateKey[20] = 0xbf;
        privateKey[19] = 0xe1;
        privateKey[18] = 0x0d;
        privateKey[17] = 0x41;
        privateKey[16] = 0x83;
        privateKey[15] = 0x7f;
        privateKey[14] = 0x10;
        privateKey[13] = 0x02;
        privateKey[12] = 0x7a;
        privateKey[11] = 0x90;
        privateKey[10] = 0xd7;
        privateKey[9] = 0xbb;
        privateKey[8] = 0x75;
        privateKey[7] = 0x34;
        privateKey[6] = 0x94;
        privateKey[5] = 0x90;
        privateKey[4] = 0x01;
        privateKey[3] = 0x8c;
        privateKey[2] = 0xf7;
        privateKey[1] = 0x2d;
        privateKey[0] = 0x07;
        k[31] = 0x24;
        k[30] = 0xfc;
        k[29] = 0x90;
        k[28] = 0xe1;
        k[27] = 0xda;
        k[26] = 0x13;
        k[25] = 0xf1;
        k[24] = 0x7e;
        k[23] = 0xf9;
        k[22] = 0xfe;
        k[21] = 0x84;
        k[20] = 0xcc;
        k[19] = 0x96;
        k[18] = 0xb9;
        k[17] = 0x47;
        k[16] = 0x1e;
        k[15] = 0xd1;
        k[14] = 0xaa;
        k[13] = 0xac;
        k[12] = 0x17;
        k[11] = 0xe3;
        k[10] = 0xa4;
        k[9] = 0xba;
        k[8] = 0xe3;
        k[7] = 0x3a;
        k[6] = 0x11;
        k[5] = 0x5d;
        k[4] = 0xf4;
        k[3] = 0xe5;
        k[2] = 0x83;
        k[1] = 0x4f;
        k[0] = 0x18;
        expectedR[31] = 0xd7;
        expectedR[30] = 0xc5;
        expectedR[29] = 0x62;
        expectedR[28] = 0x37;
        expectedR[27] = 0x0a;
        expectedR[26] = 0xf6;
        expectedR[25] = 0x17;
        expectedR[24] = 0xb5;
        expectedR[23] = 0x81;
        expectedR[22] = 0xc8;
        expectedR[21] = 0x4a;
        expectedR[20] = 0x24;
        expectedR[19] = 0x68;
        expectedR[18] = 0xcc;
        expectedR[17] = 0x8b;
        expectedR[16] = 0xd5;
        expectedR[15] = 0x0b;
        expectedR[14] = 0xb1;
        expectedR[13] = 0xcb;
        expectedR[12] = 0xf3;
        expectedR[11] = 0x22;
        expectedR[10] = 0xde;
        expectedR[9] = 0x41;
        expectedR[8] = 0xb7;
        expectedR[7] = 0x88;
        expectedR[6] = 0x7c;
        expectedR[5] = 0xe0;
        expectedR[4] = 0x7c;
        expectedR[3] = 0x0e;
        expectedR[2] = 0x58;
        expectedR[1] = 0x84;
        expectedR[0] = 0xca;
        expectedS[31] = 0xb4;
        expectedS[30] = 0x6d;
        expectedS[29] = 0x9f;
        expectedS[28] = 0x2d;
        expectedS[27] = 0x8c;
        expectedS[26] = 0x4b;
        expectedS[25] = 0xf8;
        expectedS[24] = 0x35;
        expectedS[23] = 0x46;
        expectedS[22] = 0xff;
        expectedS[21] = 0x17;
        expectedS[20] = 0x8f;
        expectedS[19] = 0x1d;
        expectedS[18] = 0x78;
        expectedS[17] = 0x93;
        expectedS[16] = 0x7c;
        expectedS[15] = 0x00;
        expectedS[14] = 0x8d;
        expectedS[13] = 0x64;
        expectedS[12] = 0xe8;
        expectedS[11] = 0xec;
        expectedS[10] = 0xc5;
        expectedS[9] = 0xcb;
        expectedS[8] = 0xb8;
        expectedS[7] = 0x25;
        expectedS[6] = 0xcb;
        expectedS[5] = 0x21;
        expectedS[4] = 0xd9;
        expectedS[3] = 0x4d;
        expectedS[2] = 0x67;
        expectedS[1] = 0x0d;
        expectedS[0] = 0x89;


    uint64_t flag = Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign_nist(result, m, privateKey, k);
    
    bool flagCorrectR = true;
    for (int i = 0; i < 32; i++)
        flagCorrectR = flagCorrectR && (result[i] == expectedR[i]);

    bool flagCorrectS = true;
    for (int i = 0; i < 32; i++)
        flagCorrectS = flagCorrectS && (result[i + 32] == expectedS[i]);


    uint64_t expectedResult = 0x0;
      if (flag == expectedResult && flagCorrectR && flagCorrectS)
        printf("%s\n", "Test3: passed");
      else
        printf("%s\n", "Test3: failed");

}

void testEcdsaSignature4()
{    
    uint8_t* m = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* privateKey = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* k = (uint8_t *) malloc (sizeof (uint8_t) * 32);

    uint8_t* result = (uint8_t *) malloc (sizeof (uint8_t) * 64);

    uint8_t* expectedR = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    uint8_t* expectedS = (uint8_t*) malloc (sizeof (uint8_t) * 32);

        m[31] = 0x33;
        m[30] = 0x60;
        m[29] = 0xd6;
        m[28] = 0x99;
        m[27] = 0x22;
        m[26] = 0x2f;
        m[25] = 0x21;
        m[24] = 0x84;
        m[23] = 0x08;
        m[22] = 0x27;
        m[21] = 0xcf;
        m[20] = 0x69;
        m[19] = 0x8d;
        m[18] = 0x7c;
        m[17] = 0xb6;
        m[16] = 0x35;
        m[15] = 0xbe;
        m[14] = 0xe5;
        m[13] = 0x7d;
        m[12] = 0xc8;
        m[11] = 0x0c;
        m[10] = 0xd7;
        m[9] = 0x73;
        m[8] = 0x3b;
        m[7] = 0x68;
        m[6] = 0x2d;
        m[5] = 0x41;
        m[4] = 0xb5;
        m[3] = 0x5b;
        m[2] = 0x66;
        m[1] = 0x6e;
        m[0] = 0x22;

        privateKey[31] = 0x53;
        privateKey[30] = 0xa0;
        privateKey[29] = 0xe8;
        privateKey[28] = 0xa8;
        privateKey[27] = 0xfe;
        privateKey[26] = 0x93;
        privateKey[25] = 0xdb;
        privateKey[24] = 0x01;
        privateKey[23] = 0xe7;
        privateKey[22] = 0xae;
        privateKey[21] = 0x94;
        privateKey[20] = 0xe1;
        privateKey[19] = 0xa9;
        privateKey[18] = 0x88;
        privateKey[17] = 0x2a;
        privateKey[16] = 0x10;
        privateKey[15] = 0x2e;
        privateKey[14] = 0xbd;
        privateKey[13] = 0x07;
        privateKey[12] = 0x9b;
        privateKey[11] = 0x3a;
        privateKey[10] = 0x53;
        privateKey[9] = 0x58;
        privateKey[8] = 0x27;
        privateKey[7] = 0xd5;
        privateKey[6] = 0x83;
        privateKey[5] = 0x62;
        privateKey[4] = 0x6c;
        privateKey[3] = 0x27;
        privateKey[2] = 0x2d;
        privateKey[1] = 0x28;
        privateKey[0] = 0x0d;

        k[31] = 0x5d;
        k[30] = 0x83;
        k[29] = 0x3e;
        k[28] = 0x8d;
        k[27] = 0x24;
        k[26] = 0xcc;
        k[25] = 0x7a;
        k[24] = 0x40;
        k[23] = 0x2d;
        k[22] = 0x7e;
        k[21] = 0xe7;
        k[20] = 0xec;
        k[19] = 0x85;
        k[18] = 0x2a;
        k[17] = 0x35;
        k[16] = 0x87;
        k[15] = 0xcd;
        k[14] = 0xde;
        k[13] = 0xb4;
        k[12] = 0x83;
        k[11] = 0x58;
        k[10] = 0xce;
        k[9] = 0xa7;
        k[8] = 0x1b;
        k[7] = 0x0b;
        k[6] = 0xed;
        k[5] = 0xb8;
        k[4] = 0xfa;
        k[3] = 0xbe;
        k[2] = 0x84;
        k[1] = 0xe0;
        k[0] = 0xc4;

        expectedR[31] = 0x18;
        expectedR[30] = 0xca;
        expectedR[29] = 0xaf;
        expectedR[28] = 0x7b;
        expectedR[27] = 0x66;
        expectedR[26] = 0x35;
        expectedR[25] = 0x07;
        expectedR[24] = 0xa8;
        expectedR[23] = 0xbc;
        expectedR[22] = 0xd9;
        expectedR[21] = 0x92;
        expectedR[20] = 0xb8;
        expectedR[19] = 0x36;
        expectedR[18] = 0xde;
        expectedR[17] = 0xc9;
        expectedR[16] = 0xdc;
        expectedR[15] = 0x57;
        expectedR[14] = 0x03;
        expectedR[13] = 0xc0;
        expectedR[12] = 0x80;
        expectedR[11] = 0xaf;
        expectedR[10] = 0x5e;
        expectedR[9] = 0x51;
        expectedR[8] = 0xdf;
        expectedR[7] = 0xa3;
        expectedR[6] = 0xa9;
        expectedR[5] = 0xa7;
        expectedR[4] = 0xc3;
        expectedR[3] = 0x87;
        expectedR[2] = 0x18;
        expectedR[1] = 0x26;
        expectedR[0] = 0x04;

        expectedS[31] = 0x77;
        expectedS[30] = 0xc6;
        expectedS[29] = 0x89;
        expectedS[28] = 0x28;
        expectedS[27] = 0xac;
        expectedS[26] = 0x3b;
        expectedS[25] = 0x88;
        expectedS[24] = 0xd9;
        expectedS[23] = 0x85;
        expectedS[22] = 0xfb;
        expectedS[21] = 0x43;
        expectedS[20] = 0xfb;
        expectedS[19] = 0x61;
        expectedS[18] = 0x5f;
        expectedS[17] = 0xb7;
        expectedS[16] = 0xff;
        expectedS[15] = 0x45;
        expectedS[14] = 0xc1;
        expectedS[13] = 0x8b;
        expectedS[12] = 0xa5;
        expectedS[11] = 0xc8;
        expectedS[10] = 0x1a;
        expectedS[9] = 0xf7;
        expectedS[8] = 0x96;
        expectedS[7] = 0xc6;
        expectedS[6] = 0x13;
        expectedS[5] = 0xdf;
        expectedS[4] = 0xa9;
        expectedS[3] = 0x83;
        expectedS[2] = 0x52;
        expectedS[1] = 0xd2;
        expectedS[0] = 0x9c;

    uint64_t flag = Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign_nist(result, m, privateKey, k);
    
    bool flagCorrectR = true;
    for (int i = 0; i < 32; i++)
        flagCorrectR = flagCorrectR && (result[i] == expectedR[i]);

    bool flagCorrectS = true;
    for (int i = 0; i < 32; i++)
        flagCorrectS = flagCorrectS && (result[i + 32] == expectedS[i]);


    uint64_t expectedResult = 0x0;
      if (flag == expectedResult && flagCorrectR && flagCorrectS)
        printf("%s\n", "Test4: passed");
      else
        printf("%s\n", "Test4: failed");

}

void testEcdsaSignature5()
{    
    uint8_t* m = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* privateKey = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* k = (uint8_t *) malloc (sizeof (uint8_t) * 32);

    uint8_t* result = (uint8_t *) malloc (sizeof (uint8_t) * 64);

    uint8_t* expectedR = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    uint8_t* expectedS = (uint8_t*) malloc (sizeof (uint8_t) * 32);

        m[31] = 0xc4;
        m[30] = 0x13;
        m[29] = 0xc4;
        m[28] = 0x90;
        m[27] = 0x8c;
        m[26] = 0xd0;
        m[25] = 0xbc;
        m[24] = 0x6d;
        m[23] = 0x8e;
        m[22] = 0x32;
        m[21] = 0x00;
        m[20] = 0x1a;
        m[19] = 0xa1;
        m[18] = 0x03;
        m[17] = 0x04;
        m[16] = 0x3b;
        m[15] = 0x2c;
        m[14] = 0xf5;
        m[13] = 0xbe;
        m[12] = 0x7f;
        m[11] = 0xcb;
        m[10] = 0xd6;
        m[9] = 0x1a;
        m[8] = 0x5c;
        m[7] = 0xec;
        m[6] = 0x94;
        m[5] = 0x88;
        m[4] = 0xc3;
        m[3] = 0xa5;
        m[2] = 0x77;
        m[1] = 0xca;
        m[0] = 0x57;

        privateKey[31] = 0x4a;
        privateKey[30] = 0xf1;
        privateKey[29] = 0x07;
        privateKey[28] = 0xe8;
        privateKey[27] = 0xe2;
        privateKey[26] = 0x19;
        privateKey[25] = 0x4c;
        privateKey[24] = 0x83;
        privateKey[23] = 0x0f;
        privateKey[22] = 0xfb;
        privateKey[21] = 0x71;
        privateKey[20] = 0x2a;
        privateKey[19] = 0x65;
        privateKey[18] = 0x51;
        privateKey[17] = 0x1b;
        privateKey[16] = 0xc9;
        privateKey[15] = 0x18;
        privateKey[14] = 0x6a;
        privateKey[13] = 0x13;
        privateKey[12] = 0x30;
        privateKey[11] = 0x07;
        privateKey[10] = 0x85;
        privateKey[9] = 0x5b;
        privateKey[8] = 0x49;
        privateKey[7] = 0xab;
        privateKey[6] = 0x4b;
        privateKey[5] = 0x38;
        privateKey[4] = 0x33;
        privateKey[3] = 0xae;
        privateKey[2] = 0xfc;
        privateKey[1] = 0x4a;
        privateKey[0] = 0x1d;

        k[31] = 0xe1;
        k[30] = 0x8f;
        k[29] = 0x96;
        k[28] = 0xf8;
        k[27] = 0x4d;
        k[26] = 0xfa;
        k[25] = 0x2f;
        k[24] = 0xd3;
        k[23] = 0xcd;
        k[22] = 0xfa;
        k[21] = 0xec;
        k[20] = 0x91;
        k[19] = 0x59;
        k[18] = 0xd4;
        k[17] = 0xc3;
        k[16] = 0x38;
        k[15] = 0xcd;
        k[14] = 0x54;
        k[13] = 0xad;
        k[12] = 0x31;
        k[11] = 0x41;
        k[10] = 0x34;
        k[9] = 0xf0;
        k[8] = 0xb3;
        k[7] = 0x1e;
        k[6] = 0x20;
        k[5] = 0x59;
        k[4] = 0x1f;
        k[3] = 0xc2;
        k[2] = 0x38;
        k[1] = 0xd0;
        k[0] = 0xab;

        expectedR[31] = 0x85;
        expectedR[30] = 0x24;
        expectedR[29] = 0xc5;
        expectedR[28] = 0x02;
        expectedR[27] = 0x4e;
        expectedR[26] = 0x2d;
        expectedR[25] = 0x9a;
        expectedR[24] = 0x73;
        expectedR[23] = 0xbd;
        expectedR[22] = 0xe8;
        expectedR[21] = 0xc7;
        expectedR[20] = 0x2d;
        expectedR[19] = 0x91;
        expectedR[18] = 0x29;
        expectedR[17] = 0xf5;
        expectedR[16] = 0x78;
        expectedR[15] = 0x73;
        expectedR[14] = 0xbb;
        expectedR[13] = 0xad;
        expectedR[12] = 0x0e;
        expectedR[11] = 0xd0;
        expectedR[10] = 0x52;
        expectedR[9] = 0x15;
        expectedR[8] = 0xa3;
        expectedR[7] = 0x72;
        expectedR[6] = 0xa8;
        expectedR[5] = 0x4f;
        expectedR[4] = 0xdb;
        expectedR[3] = 0xc7;
        expectedR[2] = 0x8f;
        expectedR[1] = 0x2e;
        expectedR[0] = 0x68;

        expectedS[31] = 0xd1;
        expectedS[30] = 0x8c;
        expectedS[29] = 0x2c;
        expectedS[28] = 0xaf;
        expectedS[27] = 0x3b;
        expectedS[26] = 0x10;
        expectedS[25] = 0x72;
        expectedS[24] = 0xf8;
        expectedS[23] = 0x70;
        expectedS[22] = 0x64;
        expectedS[21] = 0xec;
        expectedS[20] = 0x5e;
        expectedS[19] = 0x89;
        expectedS[18] = 0x53;
        expectedS[17] = 0xf5;
        expectedS[16] = 0x13;
        expectedS[15] = 0x01;
        expectedS[14] = 0xca;
        expectedS[13] = 0xda;
        expectedS[12] = 0x03;
        expectedS[11] = 0x46;
        expectedS[10] = 0x9c;
        expectedS[9] = 0x64;
        expectedS[8] = 0x02;
        expectedS[7] = 0x44;
        expectedS[6] = 0x76;
        expectedS[5] = 0x03;
        expectedS[4] = 0x28;
        expectedS[3] = 0xeb;
        expectedS[2] = 0x5a;
        expectedS[1] = 0x05;
        expectedS[0] = 0xcb;


    uint64_t flag = Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign_nist(result, m, privateKey, k);
    
    bool flagCorrectR = true;
    for (int i = 0; i < 32; i++)
        flagCorrectR = flagCorrectR && (result[i] == expectedR[i]);

    bool flagCorrectS = true;
    for (int i = 0; i < 32; i++)
        flagCorrectS = flagCorrectS && (result[i + 32] == expectedS[i]);


    uint64_t expectedResult = 0x0;
      if (flag == expectedResult && flagCorrectR && flagCorrectS)
        printf("%s\n", "Test5: passed");
      else
        printf("%s\n", "Test5: failed");

}


void testEcdsaSignature6()
{    
    uint8_t* m = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* privateKey = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* k = (uint8_t *) malloc (sizeof (uint8_t) * 32);

    uint8_t* result = (uint8_t *) malloc (sizeof (uint8_t) * 64);

    uint8_t* expectedR = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    uint8_t* expectedS = (uint8_t*) malloc (sizeof (uint8_t) * 32);

        m[31] = 0x88;
        m[30] = 0xfc;
        m[29] = 0x1e;
        m[28] = 0x7d;
        m[27] = 0x84;
        m[26] = 0x97;
        m[25] = 0x94;
        m[24] = 0xfc;
        m[23] = 0x51;
        m[22] = 0xb1;
        m[21] = 0x35;
        m[20] = 0xfa;
        m[19] = 0x13;
        m[18] = 0x5d;
        m[17] = 0xee;
        m[16] = 0xc0;
        m[15] = 0xdb;
        m[14] = 0x02;
        m[13] = 0xb8;
        m[12] = 0x6c;
        m[11] = 0x3c;
        m[10] = 0xd8;
        m[9] = 0xce;
        m[8] = 0xbd;
        m[7] = 0xaa;
        m[6] = 0x79;
        m[5] = 0xe8;
        m[4] = 0x68;
        m[3] = 0x9e;
        m[2] = 0x5b;
        m[1] = 0x28;
        m[0] = 0x98;
        privateKey[31] = 0x78;
        privateKey[30] = 0xdf;
        privateKey[29] = 0xaa;
        privateKey[28] = 0x09;
        privateKey[27] = 0xf1;
        privateKey[26] = 0x07;
        privateKey[25] = 0x68;
        privateKey[24] = 0x50;
        privateKey[23] = 0xb3;
        privateKey[22] = 0xe2;
        privateKey[21] = 0x06;
        privateKey[20] = 0xe4;
        privateKey[19] = 0x77;
        privateKey[18] = 0x49;
        privateKey[17] = 0x4c;
        privateKey[16] = 0xdd;
        privateKey[15] = 0xcf;
        privateKey[14] = 0xb8;
        privateKey[13] = 0x22;
        privateKey[12] = 0xaa;
        privateKey[11] = 0xa0;
        privateKey[10] = 0x12;
        privateKey[9] = 0x84;
        privateKey[8] = 0x75;
        privateKey[7] = 0x05;
        privateKey[6] = 0x35;
        privateKey[5] = 0x92;
        privateKey[4] = 0xc4;
        privateKey[3] = 0x8e;
        privateKey[2] = 0xba;
        privateKey[1] = 0xf4;
        privateKey[0] = 0xab;
        k[31] = 0x29;
        k[30] = 0x55;
        k[29] = 0x44;
        k[28] = 0xdb;
        k[27] = 0xb2;
        k[26] = 0xda;
        k[25] = 0x3d;
        k[24] = 0xa1;
        k[23] = 0x70;
        k[22] = 0x74;
        k[21] = 0x1c;
        k[20] = 0x9b;
        k[19] = 0x2c;
        k[18] = 0x65;
        k[17] = 0x51;
        k[16] = 0xd4;
        k[15] = 0x0a;
        k[14] = 0xf7;
        k[13] = 0xed;
        k[12] = 0x4e;
        k[11] = 0x89;
        k[10] = 0x14;
        k[9] = 0x45;
        k[8] = 0xf1;
        k[7] = 0x1a;
        k[6] = 0x02;
        k[5] = 0xb6;
        k[4] = 0x6a;
        k[3] = 0x5c;
        k[2] = 0x25;
        k[1] = 0x8a;
        k[0] = 0x77;
        expectedR[31] = 0xc5;
        expectedR[30] = 0xa1;
        expectedR[29] = 0x86;
        expectedR[28] = 0xd7;
        expectedR[27] = 0x2d;
        expectedR[26] = 0xf4;
        expectedR[25] = 0x52;
        expectedR[24] = 0x01;
        expectedR[23] = 0x54;
        expectedR[22] = 0x80;
        expectedR[21] = 0xf7;
        expectedR[20] = 0xf3;
        expectedR[19] = 0x38;
        expectedR[18] = 0x97;
        expectedR[17] = 0x0b;
        expectedR[16] = 0xfe;
        expectedR[15] = 0x82;
        expectedR[14] = 0x50;
        expectedR[13] = 0x87;
        expectedR[12] = 0xf0;
        expectedR[11] = 0x5c;
        expectedR[10] = 0x00;
        expectedR[9] = 0x88;
        expectedR[8] = 0xd9;
        expectedR[7] = 0x53;
        expectedR[6] = 0x05;
        expectedR[5] = 0xf8;
        expectedR[4] = 0x7a;
        expectedR[3] = 0xac;
        expectedR[2] = 0xc9;
        expectedR[1] = 0xb2;
        expectedR[0] = 0x54;

        expectedS[31] = 0x84;
        expectedS[30] = 0xa5;
        expectedS[29] = 0x8f;
        expectedS[28] = 0x9e;
        expectedS[27] = 0x9d;
        expectedS[26] = 0x9e;
        expectedS[25] = 0x73;
        expectedS[24] = 0x53;
        expectedS[23] = 0x44;
        expectedS[22] = 0xb3;
        expectedS[21] = 0x16;
        expectedS[20] = 0xb1;
        expectedS[19] = 0xaa;
        expectedS[18] = 0x1a;
        expectedS[17] = 0xb5;
        expectedS[16] = 0x18;
        expectedS[15] = 0x56;
        expectedS[14] = 0x65;
        expectedS[13] = 0xb8;
        expectedS[12] = 0x51;
        expectedS[11] = 0x47;
        expectedS[10] = 0xdc;
        expectedS[9] = 0x82;
        expectedS[8] = 0xd9;
        expectedS[7] = 0x2e;
        expectedS[6] = 0x96;
        expectedS[5] = 0x9d;
        expectedS[4] = 0x7b;
        expectedS[3] = 0xee;
        expectedS[2] = 0x31;
        expectedS[1] = 0xca;
        expectedS[0] = 0x30;



    uint64_t flag = Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign_nist(result, m, privateKey, k);
    
    bool flagCorrectR = true;
    for (int i = 0; i < 32; i++)
        flagCorrectR = flagCorrectR && (result[i] == expectedR[i]);

    bool flagCorrectS = true;
    for (int i = 0; i < 32; i++)
        flagCorrectS = flagCorrectS && (result[i + 32] == expectedS[i]);


    uint64_t expectedResult = 0x0;
      if (flag == expectedResult && flagCorrectR && flagCorrectS)
        printf("%s\n", "Test6: passed");
      else
        printf("%s\n", "Test6: failed");

}


void testEcdsaSignature7()
{    
    uint8_t* m = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* privateKey = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* k = (uint8_t *) malloc (sizeof (uint8_t) * 32);

    uint8_t* result = (uint8_t *) malloc (sizeof (uint8_t) * 64);

    uint8_t* expectedR = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    uint8_t* expectedS = (uint8_t*) malloc (sizeof (uint8_t) * 32);

        m[31] = 0x41;
        m[30] = 0xfa;
        m[29] = 0x8d;
        m[28] = 0x8b;
        m[27] = 0x4c;
        m[26] = 0xd0;
        m[25] = 0xa5;
        m[24] = 0xfd;
        m[23] = 0xf0;
        m[22] = 0x21;
        m[21] = 0xf4;
        m[20] = 0xe4;
        m[19] = 0x82;
        m[18] = 0x9d;
        m[17] = 0x6d;
        m[16] = 0x1e;
        m[15] = 0x99;
        m[14] = 0x6b;
        m[13] = 0xab;
        m[12] = 0x6b;
        m[11] = 0x4a;
        m[10] = 0x19;
        m[9] = 0xdc;
        m[8] = 0xb8;
        m[7] = 0x55;
        m[6] = 0x85;
        m[5] = 0xfe;
        m[4] = 0x76;
        m[3] = 0xc5;
        m[2] = 0x82;
        m[1] = 0xd2;
        m[0] = 0xbc;

        privateKey[31] = 0x80;
        privateKey[30] = 0xe6;
        privateKey[29] = 0x92;
        privateKey[28] = 0xe3;
        privateKey[27] = 0xeb;
        privateKey[26] = 0x9f;
        privateKey[25] = 0xcd;
        privateKey[24] = 0x8c;
        privateKey[23] = 0x7d;
        privateKey[22] = 0x44;
        privateKey[21] = 0xe7;
        privateKey[20] = 0xde;
        privateKey[19] = 0x9f;
        privateKey[18] = 0x7a;
        privateKey[17] = 0x59;
        privateKey[16] = 0x52;
        privateKey[15] = 0x68;
        privateKey[14] = 0x64;
        privateKey[13] = 0x07;
        privateKey[12] = 0xf9;
        privateKey[11] = 0x00;
        privateKey[10] = 0x25;
        privateKey[9] = 0xa1;
        privateKey[8] = 0xd8;
        privateKey[7] = 0x7e;
        privateKey[6] = 0x52;
        privateKey[5] = 0xc7;
        privateKey[4] = 0x09;
        privateKey[3] = 0x6a;
        privateKey[2] = 0x62;
        privateKey[1] = 0x61;
        privateKey[0] = 0x8a;

        k[31] = 0x7c;
        k[30] = 0x80;
        k[29] = 0xfd;
        k[28] = 0x66;
        k[27] = 0xd6;
        k[26] = 0x2c;
        k[25] = 0xc0;
        k[24] = 0x76;
        k[23] = 0xce;
        k[22] = 0xf2;
        k[21] = 0xd0;
        k[20] = 0x30;
        k[19] = 0xc1;
        k[18] = 0x7c;
        k[17] = 0x0a;
        k[16] = 0x69;
        k[15] = 0xc9;
        k[14] = 0x96;
        k[13] = 0x11;
        k[12] = 0x54;
        k[11] = 0x9c;
        k[10] = 0xb3;
        k[9] = 0x2c;
        k[8] = 0x4f;
        k[7] = 0xf6;
        k[6] = 0x62;
        k[5] = 0x47;
        k[4] = 0x5a;
        k[3] = 0xdb;
        k[2] = 0xe8;
        k[1] = 0x4b;
        k[0] = 0x22;

        expectedR[31] = 0x9d;
        expectedR[30] = 0x0c;
        expectedR[29] = 0x6a;
        expectedR[28] = 0xfb;
        expectedR[27] = 0x6d;
        expectedR[26] = 0xf3;
        expectedR[25] = 0xbc;
        expectedR[24] = 0xed;
        expectedR[23] = 0x45;
        expectedR[22] = 0x5b;
        expectedR[21] = 0x45;
        expectedR[20] = 0x9c;
        expectedR[19] = 0xc2;
        expectedR[18] = 0x13;
        expectedR[17] = 0x87;
        expectedR[16] = 0xe1;
        expectedR[15] = 0x49;
        expectedR[14] = 0x29;
        expectedR[13] = 0x39;
        expectedR[12] = 0x26;
        expectedR[11] = 0x64;
        expectedR[10] = 0xbb;
        expectedR[9] = 0x87;
        expectedR[8] = 0x41;
        expectedR[7] = 0xa3;
        expectedR[6] = 0x69;
        expectedR[5] = 0x3a;
        expectedR[4] = 0x17;
        expectedR[3] = 0x95;
        expectedR[2] = 0xca;
        expectedR[1] = 0x69;
        expectedR[0] = 0x02;

        expectedS[31] = 0xd7;
        expectedS[30] = 0xf9;
        expectedS[29] = 0xdd;
        expectedS[28] = 0xd1;
        expectedS[27] = 0x91;
        expectedS[26] = 0xf1;
        expectedS[25] = 0xf4;
        expectedS[24] = 0x12;
        expectedS[23] = 0x86;
        expectedS[22] = 0x94;
        expectedS[21] = 0x29;
        expectedS[20] = 0x20;
        expectedS[19] = 0x9e;
        expectedS[18] = 0xe3;
        expectedS[17] = 0x81;
        expectedS[16] = 0x4c;
        expectedS[15] = 0x75;
        expectedS[14] = 0xc7;
        expectedS[13] = 0x2f;
        expectedS[12] = 0xa4;
        expectedS[11] = 0x6a;
        expectedS[10] = 0x9c;
        expectedS[9] = 0xcc;
        expectedS[8] = 0xf8;
        expectedS[7] = 0x04;
        expectedS[6] = 0xa2;
        expectedS[5] = 0xf5;
        expectedS[4] = 0xcc;
        expectedS[3] = 0x0b;
        expectedS[2] = 0x7e;
        expectedS[1] = 0x73;
        expectedS[0] = 0x9f;


    uint64_t flag = Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign_nist(result, m, privateKey, k);
    
    bool flagCorrectR = true;
    for (int i = 0; i < 32; i++)
        flagCorrectR = flagCorrectR && (result[i] == expectedR[i]);

    bool flagCorrectS = true;
    for (int i = 0; i < 32; i++)
        flagCorrectS = flagCorrectS && (result[i + 32] == expectedS[i]);


    uint64_t expectedResult = 0x0;
      if (flag == expectedResult && flagCorrectR && flagCorrectS)
        printf("%s\n", "Test7: passed");
      else
        printf("%s\n", "Test7: failed");

}


void testEcdsaSignature8()
{    
    uint8_t* m = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* privateKey = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* k = (uint8_t *) malloc (sizeof (uint8_t) * 32);

    uint8_t* result = (uint8_t *) malloc (sizeof (uint8_t) * 64);

    uint8_t* expectedR = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    uint8_t* expectedS = (uint8_t*) malloc (sizeof (uint8_t) * 32);

        m[31] = 0x2d;
        m[30] = 0x72;
        m[29] = 0x94;
        m[28] = 0x7c;
        m[27] = 0x17;
        m[26] = 0x31;
        m[25] = 0x54;
        m[24] = 0x3b;
        m[23] = 0x3d;
        m[22] = 0x62;
        m[21] = 0x49;
        m[20] = 0x08;
        m[19] = 0x66;
        m[18] = 0xa8;
        m[17] = 0x93;
        m[16] = 0x95;
        m[15] = 0x27;
        m[14] = 0x36;
        m[13] = 0x75;
        m[12] = 0x77;
        m[11] = 0x46;
        m[10] = 0xd9;
        m[9] = 0xba;
        m[8] = 0xe1;
        m[7] = 0x3e;
        m[6] = 0x71;
        m[5] = 0x90;
        m[4] = 0x79;
        m[3] = 0x29;
        m[2] = 0x9a;
        m[1] = 0xe1;
        m[0] = 0x92;

        privateKey[31] = 0x5e;
        privateKey[30] = 0x66;
        privateKey[29] = 0x6c;
        privateKey[28] = 0x0d;
        privateKey[27] = 0xb0;
        privateKey[26] = 0x21;
        privateKey[25] = 0x4c;
        privateKey[24] = 0x3b;
        privateKey[23] = 0x62;
        privateKey[22] = 0x7a;
        privateKey[21] = 0x8e;
        privateKey[20] = 0x48;
        privateKey[19] = 0x54;
        privateKey[18] = 0x1c;
        privateKey[17] = 0xc8;
        privateKey[16] = 0x4a;
        privateKey[15] = 0x8b;
        privateKey[14] = 0x6f;
        privateKey[13] = 0xd1;
        privateKey[12] = 0x5f;
        privateKey[11] = 0x30;
        privateKey[10] = 0x0d;
        privateKey[9] = 0xa4;
        privateKey[8] = 0xdf;
        privateKey[7] = 0xf5;
        privateKey[6] = 0xd1;
        privateKey[5] = 0x8a;
        privateKey[4] = 0xec;
        privateKey[3] = 0x6c;
        privateKey[2] = 0x55;
        privateKey[1] = 0xb8;
        privateKey[0] = 0x81;

        k[31] = 0x2e;
        k[30] = 0x76;
        k[29] = 0x25;
        k[28] = 0xa4;
        k[27] = 0x88;
        k[26] = 0x74;
        k[25] = 0xd8;
        k[24] = 0x6c;
        k[23] = 0x9e;
        k[22] = 0x46;
        k[21] = 0x7f;
        k[20] = 0x89;
        k[19] = 0x0a;
        k[18] = 0xaa;
        k[17] = 0x7c;
        k[16] = 0xd6;
        k[15] = 0xeb;
        k[14] = 0xdf;
        k[13] = 0x71;
        k[12] = 0xc0;
        k[11] = 0x10;
        k[10] = 0x2b;
        k[9] = 0xfd;
        k[8] = 0xcf;
        k[7] = 0xa2;
        k[6] = 0x45;
        k[5] = 0x65;
        k[4] = 0xd6;
        k[3] = 0xaf;
        k[2] = 0x3f;
        k[1] = 0xdc;
        k[0] = 0xe9;

        expectedR[31] = 0x2f;
        expectedR[30] = 0x9e;
        expectedR[29] = 0x2b;
        expectedR[28] = 0x4e;
        expectedR[27] = 0x9f;
        expectedR[26] = 0x74;
        expectedR[25] = 0x7c;
        expectedR[24] = 0x65;
        expectedR[23] = 0x7f;
        expectedR[22] = 0x70;
        expectedR[21] = 0x5b;
        expectedR[20] = 0xff;
        expectedR[19] = 0xd1;
        expectedR[18] = 0x24;
        expectedR[17] = 0xee;
        expectedR[16] = 0x17;
        expectedR[15] = 0x8b;
        expectedR[14] = 0xbc;
        expectedR[13] = 0x53;
        expectedR[12] = 0x91;
        expectedR[11] = 0xc8;
        expectedR[10] = 0x6d;
        expectedR[9] = 0x05;
        expectedR[8] = 0x67;
        expectedR[7] = 0x17;
        expectedR[6] = 0xb1;
        expectedR[5] = 0x40;
        expectedR[4] = 0xc1;
        expectedR[3] = 0x53;
        expectedR[2] = 0x57;
        expectedR[1] = 0x0f;
        expectedR[0] = 0xd9;

        expectedS[31] = 0xf5;
        expectedS[30] = 0x41;
        expectedS[29] = 0x3b;
        expectedS[28] = 0xfd;
        expectedS[27] = 0x85;
        expectedS[26] = 0x94;
        expectedS[25] = 0x9d;
        expectedS[24] = 0xa8;
        expectedS[23] = 0xd8;
        expectedS[22] = 0x3d;
        expectedS[21] = 0xe8;
        expectedS[20] = 0x3a;
        expectedS[19] = 0xb0;
        expectedS[18] = 0xd1;
        expectedS[17] = 0x9b;
        expectedS[16] = 0x29;
        expectedS[15] = 0x86;
        expectedS[14] = 0x61;
        expectedS[13] = 0x3e;
        expectedS[12] = 0x22;
        expectedS[11] = 0x4d;
        expectedS[10] = 0x19;
        expectedS[9] = 0x01;
        expectedS[8] = 0xd7;
        expectedS[7] = 0x69;
        expectedS[6] = 0x19;
        expectedS[5] = 0xde;
        expectedS[4] = 0x23;
        expectedS[3] = 0xcc;
        expectedS[2] = 0xd0;
        expectedS[1] = 0x31;
        expectedS[0] = 0x99;

    uint64_t flag = Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign_nist(result, m, privateKey, k);
    
    bool flagCorrectR = true;
    for (int i = 0; i < 32; i++)
        flagCorrectR = flagCorrectR && (result[i] == expectedR[i]);

    bool flagCorrectS = true;
    for (int i = 0; i < 32; i++)
        flagCorrectS = flagCorrectS && (result[i + 32] == expectedS[i]);


    uint64_t expectedResult = 0x0;
      if (flag == expectedResult && flagCorrectR && flagCorrectS)
        printf("%s\n", "Test8: passed");
      else
        printf("%s\n", "Test8: failed");

}


void testEcdsaSignature9()
{    
    uint8_t* m = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* privateKey = (uint8_t *) malloc (sizeof (uint8_t) * 32);
    uint8_t* k = (uint8_t *) malloc (sizeof (uint8_t) * 32);

    uint8_t* result = (uint8_t *) malloc (sizeof (uint8_t) * 64);

    uint8_t* expectedR = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    uint8_t* expectedS = (uint8_t*) malloc (sizeof (uint8_t) * 32);

        m[31] = 0xe1;
        m[30] = 0x38;
        m[29] = 0xbd;
        m[28] = 0x57;
        m[27] = 0x7c;
        m[26] = 0x37;
        m[25] = 0x29;
        m[24] = 0xd0;
        m[23] = 0xe2;
        m[22] = 0x4a;
        m[21] = 0x98;
        m[20] = 0xa8;
        m[19] = 0x24;
        m[18] = 0x78;
        m[17] = 0xbc;
        m[16] = 0xc7;
        m[15] = 0x48;
        m[14] = 0x24;
        m[13] = 0x99;
        m[12] = 0xc4;
        m[11] = 0xcd;
        m[10] = 0xf7;
        m[9] = 0x34;
        m[8] = 0xa8;
        m[7] = 0x74;
        m[6] = 0xf7;
        m[5] = 0x20;
        m[4] = 0x8d;
        m[3] = 0xdb;
        m[2] = 0xc3;
        m[1] = 0xc1;
        m[0] = 0x16;

        privateKey[31] = 0xf7;
        privateKey[30] = 0x3f;
        privateKey[29] = 0x45;
        privateKey[28] = 0x52;
        privateKey[27] = 0x71;
        privateKey[26] = 0xc8;
        privateKey[25] = 0x77;
        privateKey[24] = 0xc4;
        privateKey[23] = 0xd5;
        privateKey[22] = 0x33;
        privateKey[21] = 0x46;
        privateKey[20] = 0x27;
        privateKey[19] = 0xe3;
        privateKey[18] = 0x7c;
        privateKey[17] = 0x27;
        privateKey[16] = 0x8f;
        privateKey[15] = 0x68;
        privateKey[14] = 0xd1;
        privateKey[13] = 0x43;
        privateKey[12] = 0x01;
        privateKey[11] = 0x4b;
        privateKey[10] = 0x0a;
        privateKey[9] = 0x05;
        privateKey[8] = 0xaa;
        privateKey[7] = 0x62;
        privateKey[6] = 0xf3;
        privateKey[5] = 0x08;
        privateKey[4] = 0xb2;
        privateKey[3] = 0x10;
        privateKey[2] = 0x1c;
        privateKey[1] = 0x53;
        privateKey[0] = 0x08;

        k[31] = 0x62;
        k[30] = 0xf8;
        k[29] = 0x66;
        k[28] = 0x5f;
        k[27] = 0xd6;
        k[26] = 0xe2;
        k[25] = 0x6b;
        k[24] = 0x3f;
        k[23] = 0xa0;
        k[22] = 0x69;
        k[21] = 0xe8;
        k[20] = 0x52;
        k[19] = 0x81;
        k[18] = 0x77;
        k[17] = 0x7a;
        k[16] = 0x9b;
        k[15] = 0x1f;
        k[14] = 0x0d;
        k[13] = 0xfd;
        k[12] = 0x2c;
        k[11] = 0x0b;
        k[10] = 0x9f;
        k[9] = 0x54;
        k[8] = 0xa0;
        k[7] = 0x86;
        k[6] = 0xd0;
        k[5] = 0xc1;
        k[4] = 0x09;
        k[3] = 0xff;
        k[2] = 0x9f;
        k[1] = 0xd6;
        k[0] = 0x15;

        expectedR[31] = 0x1c;
        expectedR[30] = 0xc6;
        expectedR[29] = 0x28;
        expectedR[28] = 0x53;
        expectedR[27] = 0x3d;
        expectedR[26] = 0x00;
        expectedR[25] = 0x04;
        expectedR[24] = 0xb2;
        expectedR[23] = 0xb2;
        expectedR[22] = 0x0e;
        expectedR[21] = 0x7f;
        expectedR[20] = 0x4b;
        expectedR[19] = 0xaa;
        expectedR[18] = 0xd0;
        expectedR[17] = 0xb8;
        expectedR[16] = 0xbb;
        expectedR[15] = 0x5e;
        expectedR[14] = 0x06;
        expectedR[13] = 0x73;
        expectedR[12] = 0xdb;
        expectedR[11] = 0x15;
        expectedR[10] = 0x9b;
        expectedR[9] = 0xbc;
        expectedR[8] = 0xcf;
        expectedR[7] = 0x92;
        expectedR[6] = 0x49;
        expectedR[5] = 0x1a;
        expectedR[4] = 0xef;
        expectedR[3] = 0x61;
        expectedR[2] = 0xfc;
        expectedR[1] = 0x96;
        expectedR[0] = 0x20;

        expectedS[31] = 0x88;
        expectedS[30] = 0x0e;
        expectedS[29] = 0x0b;
        expectedS[28] = 0xbf;
        expectedS[27] = 0x82;
        expectedS[26] = 0xa8;
        expectedS[25] = 0xcf;
        expectedS[24] = 0x81;
        expectedS[23] = 0x8e;
        expectedS[22] = 0xd4;
        expectedS[21] = 0x6b;
        expectedS[20] = 0xa0;
        expectedS[19] = 0x3c;
        expectedS[18] = 0xf0;
        expectedS[17] = 0xfc;
        expectedS[16] = 0x6c;
        expectedS[15] = 0x89;
        expectedS[14] = 0x8e;
        expectedS[13] = 0x36;
        expectedS[12] = 0xfc;
        expectedS[11] = 0xa3;
        expectedS[10] = 0x6c;
        expectedS[9] = 0xc7;
        expectedS[8] = 0xfd;
        expectedS[7] = 0xb1;
        expectedS[6] = 0xd2;
        expectedS[5] = 0xdb;
        expectedS[4] = 0x75;
        expectedS[3] = 0x03;
        expectedS[2] = 0x63;
        expectedS[1] = 0x44;
        expectedS[0] = 0x30;


    uint64_t flag = Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign_nist(result, m, privateKey, k);
    
    bool flagCorrectR = true;
    for (int i = 0; i < 32; i++)
        flagCorrectR = flagCorrectR && (result[i] == expectedR[i]);

    bool flagCorrectS = true;
    for (int i = 0; i < 32; i++)
        flagCorrectS = flagCorrectS && (result[i + 32] == expectedS[i]);


    uint64_t expectedResult = 0x0;
      if (flag == expectedResult && flagCorrectR && flagCorrectS)
        printf("%s\n", "Test9: passed");
      else
        printf("%s\n", "Test9: failed");

}
