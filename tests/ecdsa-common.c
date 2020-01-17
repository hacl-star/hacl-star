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

#include "Hacl_ECDSA.h"


bool testEcdsaSignature0()
{

    uint8_t* result = (uint8_t *) malloc (sizeof (uint8_t) * 64);

    uint8_t m[32] = {0x56,  0xec,  0x33,  0xa1,  0xa6,  0xe7,  0xc4,  0xdb,  0x77,  0x03,  0x90,  0x1a,  0xfb,  0x2e,  0x1e,  0x4e,  0x50,  0x09,  0xfe,  0x04,  0x72,  0x89,  0xc5,  0xc2,  0x42,  0x13,  0x6c,  0xe3,  0xb7,  0xf6,  0xac,  0x44};
    uint8_t privateKey[32] = {0x64,  0xb4,  0x72,  0xda,  0x6d,  0xa5,  0x54,  0xca,  0xac,  0x3e,  0x4e,  0x0b,  0x13,  0xc8,  0x44,  0x5b,  0x1a,  0x77,  0xf4,  0x59,  0xee,  0xa8,  0x4f,  0x1f,  0x58,  0x8b,  0x5f,  0x71,  0x3d,  0x42,  0x9b,  0x51};
    uint8_t k[32] = {0xde,  0x68,  0x2a,  0x64,  0x87,  0x07,  0x67,  0xb9,  0x33,  0x5d,  0x4f,  0x82,  0x47,  0x62,  0x4a,  0x3b,  0x7f,  0x3c,  0xe9,  0xf9,  0x45,  0xf2,  0x80,  0xa2,  0x61,  0x6a,  0x90,  0x4b,  0xb1,  0xbb,  0xa1,  0x94};
    uint8_t expectedR[32] = {0xac,  0xc2,  0xc8,  0x79,  0x6f,  0x5e,  0xbb,  0xca,  0x7a,  0x5a,  0x55,  0x6a,  0x1f,  0x6b,  0xfd,  0x2a,  0xed,  0x27,  0x95,  0x62,  0xd6,  0xe3,  0x43,  0x88,  0x5b,  0x79,  0x14,  0xb5,  0x61,  0x80,  0xac,  0xf3};
    uint8_t expectedS[32] = {0x03,  0x89,  0x05,  0xcc,  0x2a,  0xda,  0xcd,  0x3c,  0x5a,  0x17,  0x6f,  0xe9,  0x18,  0xb2,  0x97,  0xef,  0x1c,  0x37,  0xf7,  0x2b,  0x26,  0x76,  0x6c,  0x78,  0xb2,  0xa6,  0x05,  0xca,  0x19,  0x78,  0xf7,  0x8b};

    uint64_t flag = Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign_nist(result, m, privateKey, k);
    
    bool flagCorrectR = true;
    for (int i = 0; i < 32; i++)
        flagCorrectR = flagCorrectR && (result[i] == expectedR[i]);

    bool flagCorrectS = true;
    for (int i = 0; i < 32; i++)
        flagCorrectS = flagCorrectS && (result[i + 32] == expectedS[i]);


    uint64_t expectedResult = 0x0;
    return expectedResult && flagCorrectR && flagCorrectS;
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


void testEcdsaVerification0()
   {
      uint8_t* m = (uint8_t *) malloc (sizeof (uint8_t) * 128);
      m[0] = 0x06;
      m[1] = 0x9a;
      m[2] = 0x6e;
      m[3] = 0x6b;
      m[4] = 0x93;
      m[5] = 0xdf;
      m[6] = 0xee;
      m[7] = 0x6d;
      m[8] = 0xf6;
      m[9] = 0xef;
      m[10] = 0x69;
      m[11] = 0x97;
      m[12] = 0xcd;
      m[13] = 0x80;
      m[14] = 0xdd;
      m[15] = 0x21;
      m[16] = 0x82;
      m[17] = 0xc3;
      m[18] = 0x66;
      m[19] = 0x53;
      m[20] = 0xce;
      m[21] = 0xf1;
      m[22] = 0x0c;
      m[23] = 0x65;
      m[24] = 0x5d;
      m[25] = 0x52;
      m[26] = 0x45;
      m[27] = 0x85;
      m[28] = 0x65;
      m[29] = 0x54;
      m[30] = 0x62;
      m[31] = 0xd6;
      m[32] = 0x83;
      m[33] = 0x87;
      m[34] = 0x7f;
      m[35] = 0x95;
      m[36] = 0xec;
      m[37] = 0xc6;
      m[38] = 0xd6;
      m[39] = 0xc8;
      m[40] = 0x16;
      m[41] = 0x23;
      m[42] = 0xd8;
      m[43] = 0xfa;
      m[44] = 0xc4;
      m[45] = 0xe9;
      m[46] = 0x00;
      m[47] = 0xed;
      m[48] = 0x00;
      m[49] = 0x19;
      m[50] = 0x96;
      m[51] = 0x40;
      m[52] = 0x94;
      m[53] = 0xe7;
      m[54] = 0xde;
      m[55] = 0x91;
      m[56] = 0xf1;
      m[57] = 0x48;
      m[58] = 0x19;
      m[59] = 0x89;
      m[60] = 0xae;
      m[61] = 0x18;
      m[62] = 0x73;
      m[63] = 0x00;
      m[64] = 0x45;
      m[65] = 0x65;
      m[66] = 0x78;
      m[67] = 0x9c;
      m[68] = 0xbf;
      m[69] = 0x5d;
      m[70] = 0xc5;
      m[71] = 0x6c;
      m[72] = 0x62;
      m[73] = 0xae;
      m[74] = 0xdc;
      m[75] = 0x63;
      m[76] = 0xf6;
      m[77] = 0x2f;
      m[78] = 0x3b;
      m[79] = 0x89;
      m[80] = 0x4c;
      m[81] = 0x9c;
      m[82] = 0x6f;
      m[83] = 0x77;
      m[84] = 0x88;
      m[85] = 0xc8;
      m[86] = 0xec;
      m[87] = 0xaa;
      m[88] = 0xdc;
      m[89] = 0x9b;
      m[90] = 0xd0;
      m[91] = 0xe8;
      m[92] = 0x1a;
      m[93] = 0xd9;
      m[94] = 0x1b;
      m[95] = 0x2b;
      m[96] = 0x35;
      m[97] = 0x69;
      m[98] = 0xea;
      m[99] = 0x12;
      m[100] = 0x26;
      m[101] = 0x0e;
      m[102] = 0x93;
      m[103] = 0x92;
      m[104] = 0x4f;
      m[105] = 0xdd;
      m[106] = 0xdd;
      m[107] = 0x39;
      m[108] = 0x72;
      m[109] = 0xaf;
      m[110] = 0x52;
      m[111] = 0x73;
      m[112] = 0x19;
      m[113] = 0x8f;
      m[114] = 0x5e;
      m[115] = 0xfd;
      m[116] = 0xa0;
      m[117] = 0x74;
      m[118] = 0x62;
      m[119] = 0x19;
      m[120] = 0x47;
      m[121] = 0x50;
      m[122] = 0x17;
      m[123] = 0x55;
      m[124] = 0x76;
      m[125] = 0x16;
      m[126] = 0x17;
      m[127] = 0x0e;


      uint32_t mLen = 128;
      uint64_t* pubKey = (uint64_t *) malloc (sizeof (uint64_t) * 12);
      uint64_t* r = (uint64_t *) malloc (sizeof (uint64_t) * 4);
      uint64_t* s = (uint64_t *) malloc (sizeof (uint64_t) * 4);
      
      pubKey[3] = 0x5cf02a00d205bdfeul;
      pubKey[2] = 0xe2016f7421807fc3ul;
      pubKey[1] = 0x8ae69e6b7ccd064eul;
      pubKey[0] = 0xe689fc1a94a9f7d2ul;

      pubKey[7] = 0xec530ce3cc5c9d1aul;
      pubKey[6] = 0xf463f264d685afe2ul;
      pubKey[5] = 0xb4db4b5828d7e61bul;
      pubKey[4] = 0x748930f3ce622a85ul;

      r[3] =  0xdc23d130c6117fb5ul;
      r[2] =  0x751201455e99f36ful;
      r[1] =  0x59aba1a6a21cf2d0ul;
      r[0] =  0xe7481a97451d6693ul;
 
      s[3] =  0xd6ce7708c18dbf35ul;
      s[2] =  0xd4f8aa7240922dc6ul;
      s[1] =  0x823f2e7058cbc148ul;
      s[0] =  0x4fcad1599db5018cul;

      bool result = Hacl_Impl_ECDSA_ecdsa_p256_sha2_verify (mLen, m , pubKey, r, s);

      bool expectedResult = false;
      if (result == expectedResult)
        printf("%s\n", "Test4: passed");
      else
        printf("%s\n", "Test4: failed");
}

void testEcdsaVerification1()
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

      bool result = Hacl_Impl_ECDSA_ecdsa_p256_sha2_verify (mLen, m, pubKey, r, s);

      bool expectedResult = true;
      if (result == expectedResult)
        printf("%s\n", "Test0: passed");
      else
        printf("%s\n", "Test0: failed");
}

/*
Msg = e4796db5f785f207aa30d311693b3702821dff1168fd2e04c0836825aefd850d9aa60326d88cde1a23c7745351392ca2288d632c264f197d05cd424a30336c19fd09bb229654f0222fcb881a4b35c290a093ac159ce13409111ff0358411133c24f5b8e2090d6db6558afc36f06ca1f6ef779785adba68db27a409859fc4c4a0
Qx = 87f8f2b218f49845f6f10eec3877136269f5c1a54736dbdf69f89940cad41555
Qy = e15f369036f49842fac7a86c8a2b0557609776814448b8f5e84aa9f4395205e9
R = d19ff48b324915576416097d2544f7cbdf8768b1454ad20e0baac50e211f23b0
S = a3e81e59311cdfff2d4784949f7a2cb50ba6c3a91fa54710568e61aca3e847c6
Result = F (3 - S changed)
*/

void testEcdsaVerification2()
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

      bool result = Hacl_Impl_ECDSA_ecdsa_p256_sha2_verify  (mLen, m , pubKey, r, s);

      bool expectedResult = false;
      if (result == expectedResult)
        printf("%s\n", "Test1: passed");
      else
        printf("%s\n", "Test1: failed");
}

void testEcdsaVerification3()
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

      bool result = Hacl_Impl_ECDSA_ecdsa_p256_sha2_verify  (mLen, m , pubKey, r, s);

      bool expectedResult = true;
      if (result == expectedResult)
        printf("%s\n", "Test2: passed");
      else
        printf("%s\n", "Test2: failed");
}

void testEcdsaVerification4()
   {
      uint8_t* m = (uint8_t *) malloc (sizeof (uint8_t) * 128);
      m[0] = 0x60;
      m[1] = 0xcd;
      m[2] = 0x64;
      m[3] = 0xb2;
      m[4] = 0xcd;
      m[5] = 0x2b;
      m[6] = 0xe6;
      m[7] = 0xc3;
      m[8] = 0x38;
      m[9] = 0x59;
      m[10] = 0xb9;
      m[11] = 0x48;
      m[12] = 0x75;
      m[13] = 0x12;
      m[14] = 0x03;
      m[15] = 0x61;
      m[16] = 0xa2;
      m[17] = 0x40;
      m[18] = 0x85;
      m[19] = 0xf3;
      m[20] = 0x76;
      m[21] = 0x5c;
      m[22] = 0xb8;
      m[23] = 0xb2;
      m[24] = 0xbf;
      m[25] = 0x11;
      m[26] = 0xe0;
      m[27] = 0x26;
      m[28] = 0xfa;
      m[29] = 0x9d;
      m[30] = 0x88;
      m[31] = 0x55;
      m[32] = 0xdb;
      m[33] = 0xe4;
      m[34] = 0x35;
      m[35] = 0xac;
      m[36] = 0xf7;
      m[37] = 0x88;
      m[38] = 0x2e;
      m[39] = 0x84;
      m[40] = 0xf3;
      m[41] = 0xc7;
      m[42] = 0x85;
      m[43] = 0x7f;
      m[44] = 0x96;
      m[45] = 0xe2;
      m[46] = 0xba;
      m[47] = 0xab;
      m[48] = 0x4d;
      m[49] = 0x9a;
      m[50] = 0xfe;
      m[51] = 0x45;
      m[52] = 0x88;
      m[53] = 0xe4;
      m[54] = 0xa8;
      m[55] = 0x2e;
      m[56] = 0x17;
      m[57] = 0xa7;
      m[58] = 0x88;
      m[59] = 0x27;
      m[60] = 0xbf;
      m[61] = 0xdb;
      m[62] = 0x5d;
      m[63] = 0xdb;
      m[64] = 0xd1;
      m[65] = 0xc2;
      m[66] = 0x11;
      m[67] = 0xfb;
      m[68] = 0xc2;
      m[69] = 0xe6;
      m[70] = 0xd8;
      m[71] = 0x84;
      m[72] = 0xcd;
      m[73] = 0xdd;
      m[74] = 0x7c;
      m[75] = 0xb9;
      m[76] = 0xd9;
      m[77] = 0x0d;
      m[78] = 0x5b;
      m[79] = 0xf4;
      m[80] = 0xa7;
      m[81] = 0x31;
      m[82] = 0x1b;
      m[83] = 0x83;
      m[84] = 0xf3;
      m[85] = 0x52;
      m[86] = 0x50;
      m[87] = 0x80;
      m[88] = 0x33;
      m[89] = 0x81;
      m[90] = 0x2c;
      m[91] = 0x77;
      m[92] = 0x6a;
      m[93] = 0x0e;
      m[94] = 0x00;
      m[95] = 0xc0;
      m[96] = 0x03;
      m[97] = 0xc7;
      m[98] = 0xe0;
      m[99] = 0xd6;
      m[100] = 0x28;
      m[101] = 0xe5;
      m[102] = 0x07;
      m[103] = 0x36;
      m[104] = 0xc7;
      m[105] = 0x51;
      m[106] = 0x2d;
      m[107] = 0xf0;
      m[108] = 0xac;
      m[109] = 0xfa;
      m[110] = 0x9f;
      m[111] = 0x23;
      m[112] = 0x20;
      m[113] = 0xbd;
      m[114] = 0x10;
      m[115] = 0x22;
      m[116] = 0x29;
      m[117] = 0xf4;
      m[118] = 0x64;
      m[119] = 0x95;
      m[120] = 0xae;
      m[121] = 0x6d;
      m[122] = 0x08;
      m[123] = 0x57;
      m[124] = 0xcc;
      m[125] = 0x45;
      m[126] = 0x2a;
      m[127] = 0x84;


      uint32_t mLen = 128;
      uint64_t* pubKey = (uint64_t *) malloc (sizeof (uint64_t) * 12);
      uint64_t* r = (uint64_t *) malloc (sizeof (uint64_t) * 4);
      uint64_t* s = (uint64_t *) malloc (sizeof (uint64_t) * 4);
      
      pubKey[3] = 0x2d98ea01f754d34bul;
      pubKey[2] = 0xbc3003df5050200a;
      pubKey[1] = 0xbf445ec728556d7e;
      pubKey[0] = 0xd7d5c54c55552b6d;

      pubKey[7] = 0x9b52672742d637a3;
      pubKey[6] = 0x2add056dfd6d8792;
      pubKey[5] = 0xf2a33c2e69dafabe;
      pubKey[4] = 0xa09b960bc61e230a;

      r[3] =  0x06108e525f845d01;
      r[2] =  0x55bf60193222b321;
      r[1] =  0x9c98e3d49424c2fb;
      r[0] =  0x2a0987f825c17959;
 
      s[3] =  0x62b5cdd591e5b507;
      s[2] =  0xe560167ba8f6f7cd;
      s[1] =  0xa74673eb315680cb;
      s[0] =  0x89ccbc4eec477dce;

      bool result = Hacl_Impl_ECDSA_ecdsa_p256_sha2_verify  (mLen, m , pubKey, r, s);

      bool expectedResult = true;
      if (result == expectedResult)
        printf("%s\n", "Test5: passed");
      else
        printf("%s\n", "Test5: failed");
}



int main()
{
    if (!testEcdsaSignature0())
        return EXIT_FAILURE;
    return EXIT_SUCCESS;
    
    testEcdsaSignature0();
    testEcdsaSignature1();
    testEcdsaSignature2();
    testEcdsaSignature3();
    testEcdsaSignature4();
    testEcdsaSignature5();
    testEcdsaSignature6();
    testEcdsaSignature7();
    testEcdsaSignature8();
    testEcdsaSignature9();

    testEcdsaVerification0();
    testEcdsaVerification1();
    testEcdsaVerification2();
    testEcdsaVerification3();
    testEcdsaVerification4();

}