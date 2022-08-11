#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <time.h>
#include <stdbool.h>
#include "test_helpers.h"

#include "Hacl_P256.h"

#include <stdint.h>
#include <string.h>
#include <stdint.h>



#define SIZE   32
#define ROUNDS 10000

static inline bool compare(size_t len, uint8_t* comp, uint8_t* exp) {
  bool ok = true;
  for (size_t i = 0; i < len; i++)
    ok = ok & (exp[i] == comp[i]);
  return ok;
}


#include <assert.h>
#include <inttypes.h>


bool test_ecdh()
{
    static uint8_t publicKeyX1[32] = {
    0x70, 0x0c, 0x48, 0xf7, 0x7f, 0x56, 0x58, 0x4c, 0x5c, 0xc6, 0x32, 0xca, 0x65, 0x64, 0x0d, 0xb9, 0x1b, 0x6b, 0xac, 0xce, 0x3a, 0x4d, 0xf6, 0xb4, 0x2c, 0xe7, 0xcc, 0x83, 0x88, 0x33, 0xd2, 0x87 
    };

    static uint8_t publicKeyY1[32] = {
    0xdb, 0x71, 0xe5, 0x09, 0xe3, 0xfd, 0x9b, 0x06, 0x0d, 0xdb, 0x20, 0xba, 0x5c, 0x51, 0xdc, 0xc5, 0x94, 0x8d, 0x46, 0xfb, 0xf6, 0x40, 0xdf, 0xe0, 0x44, 0x17, 0x82, 0xca, 0xb8, 0x5f, 0xa4, 0xac 
    };
    
    static uint8_t privateKey[32] = {
    0x7d, 0x7d, 0xc5, 0xf7, 0x1e, 0xb2, 0x9d, 0xda, 0xf8, 0x0d, 0x62, 0x14, 0x63, 0x2e, 0xea, 0xe0, 0x3d, 0x90, 0x58, 0xaf, 0x1f, 0xb6, 0xd2, 0x2e, 0xd8, 0x0b, 0xad, 0xb6, 0x2b, 0xc1, 0xa5, 0x34 
    };

    static uint8_t privateKey1[32] = {
    0x7d, 0x7d, 0xc5, 0xf7, 0x1e, 0xb2, 0x9d, 0xda, 0xf8, 0x0d, 0x62, 0x14, 0x63, 0x2e, 0xea, 0xe0, 0x3d, 0x90, 0x58, 0xaf, 0x1f, 0xb6, 0xd2, 0x2e, 0xd8, 0x0b, 0xad, 0xb6, 0x2b, 0xc1, 0xa5, 0x34 
    };

    static uint8_t expectedPublicKeyX[32] = {
    0xea, 0xd2, 0x18, 0x59, 0x01, 0x19, 0xe8, 0x87, 0x6b, 0x29, 0x14, 0x6f, 0xf8, 0x9c, 0xa6, 0x17, 0x70, 0xc4, 0xed, 0xbb, 0xf9, 0x7d, 0x38, 0xce, 0x38, 0x5e, 0xd2, 0x81, 0xd8, 0xa6, 0xb2, 0x30 
    };
    
    static uint8_t expectedPublicKeyY[32] = {
    0x28, 0xaf, 0x61, 0x28, 0x1f, 0xd3, 0x5e, 0x2f, 0xa7, 0x00, 0x25, 0x23, 0xac, 0xc8, 0x5a, 0x42, 0x9c, 0xb0, 0x6e, 0xe6, 0x64, 0x83, 0x25, 0x38, 0x9f, 0x59, 0xed, 0xfc, 0xe1, 0x40, 0x51, 0x41 
    };

    static uint8_t expectedResult[32] = {
    0x46, 0xfc, 0x62, 0x10, 0x64, 0x20, 0xff, 0x01, 0x2e, 0x54, 0xa4, 0x34, 0xfb, 0xdd, 0x2d, 0x25, 0xcc, 0xc5, 0x85, 0x20, 0x60, 0x56, 0x1e, 0x68, 0x04, 0x0d, 0xd7, 0x77, 0x89, 0x97, 0xbd, 0x7b 
    };

    bool ok = true;

    printf("%s\n", "---------------------------------------------------------------" );

    printf("\n");

    printf("%s\n", "ECDHP256 Initiator - Montgomery Ladder");
    printf("\n");
    uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    
    
    bool successDHI = Hacl_P256_ecp256dh_i_ml(result, privateKey);
    ok = ok && successDHI;
    compare_and_print(32, result, expectedPublicKeyX);
    compare_and_print(32, result + 32, expectedPublicKeyY);


    printf("\n");



    printf("%s\n", "---------------------------------------------------------------" );

    printf("\n");

    printf("%s\n", "ECDHP256 Initiator - Radix");

    uint8_t* result_i_radix = (uint8_t*) malloc (sizeof (uint8_t) * 64);    
    successDHI = Hacl_P256_ecp256dh_i_radix(result_i_radix, privateKey);
    printf("\n");
    ok = ok && successDHI;
    compare_and_print(32, result_i_radix, expectedPublicKeyX);
    compare_and_print(32, result_i_radix + 32, expectedPublicKeyY);

    printf("\n");


    printf("%s\n", "---------------------------------------------------------------" );

    printf("\n");

    printf("%s\n", "ECDHP256 Initiator - WNAF");

    uint8_t* result_i_wnaf = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    
    successDHI = Hacl_P256_ecp256dh_i_wnaf(result_i_wnaf, privateKey);
    printf("\n");
    ok = ok && successDHI;
    compare_and_print(32, result_i_wnaf, expectedPublicKeyX);
    compare_and_print(32, result_i_wnaf + 32, expectedPublicKeyY);

    printf("\n");
    printf("%s\n", "---------------------------------------------------------------" );

    printf("\n");

    printf("%s\n", "ECDHP256 Responder - Montgomery Ladder");
    printf("\n");
    result = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    memcpy(pk, publicKeyX1,  32);
    memcpy(pk+32, publicKeyY1,  32);
       
    bool successDHR = Hacl_P256_ecp256dh_r_private_ml(result, pk, privateKey);
    ok = ok && compare_and_print(32, result, expectedResult);
    ok = ok && successDHR;

    printf("\n");
    printf("%s\n", "---------------------------------------------------------------" );

    printf("\n");
    printf("%s\n", "ECDHP256 Responder - Radix");
    printf("\n");


    result = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    memcpy(pk, publicKeyX1,  32);
    memcpy(pk+32, publicKeyY1,  32);
       
    successDHR = Hacl_P256_ecp256dh_r_private_radix(result, pk, privateKey);
    ok = ok && compare_and_print(32, result, expectedResult);
    ok = ok && successDHR;

    printf("\n");
    printf("%s\n", "---------------------------------------------------------------" );

    static uint8_t privateKey_p384[48] = {
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xc7, 0x63, 0x4d, 0x81, 0xf4, 0x37, 0x2d, 0xdf,
        0x58, 0x1a, 0xd,  0xb2, 0x48, 0xb0, 0xa7, 0x7a,
        0xec, 0xec, 0x19, 0x6a, 0xcc, 0xc5, 0x29, 0x71};

    static uint8_t expectedPublicKeyX_p384[48] = {
        0x08, 0xD9, 0x99, 0x05, 0x7B, 0xA3, 0xD2, 0xD9, 
        0x69, 0x26, 0x00, 0x45, 0xC5, 0x5B, 0x97, 0xF0,
        0x89, 0x02, 0x59, 0x59, 0xA6, 0xF4, 0x34, 0xD6, 
        0x51, 0xD2, 0x07, 0xD1, 0x9F, 0xB9, 0x6E, 0x9E, 
        0x4F, 0xE0, 0xE8, 0x6E, 0xBE, 0x0E, 0x64, 0xF8,
        0x5B, 0x96, 0xA9, 0xC7, 0x52, 0x95, 0xDF, 0x61};
        
    static uint8_t expectedPublicKeyY_p384[48] = {
        0x71, 0x7F, 0x0E, 0x05, 0xA4, 0xE4, 0xC3, 0x12, 
        0x48, 0x40, 0x17, 0x20, 0x02, 0x92, 0x45, 0x8B, 
        0x4D, 0x8A, 0x27, 0x8A, 0x43, 0x93, 0x3B, 0xC1, 
        0x6F, 0xB1, 0xAF, 0xA0, 0xDA, 0x95, 0x4B, 0xD9, 
        0xA0, 0x02, 0xBC, 0x15, 0xB2, 0xC6, 0x1D, 0xD2, 
        0x9E, 0xAF, 0xE1, 0x90, 0xF5, 0x6B, 0xF1, 0x7F};

    static uint8_t expectedResult_p384[96] = {
        0x13, 0x82, 0x51, 0xcd, 0x52, 0xac, 0x92, 0x98, 
        0xc1, 0xc8, 0xaa, 0xd9, 0x77, 0x32, 0x1d, 0xeb, 
        0x97, 0xe7, 0x09, 0xbd, 0x0b, 0x4c, 0xa0, 0xac, 
        0xa5, 0x5d, 0xc8, 0xad, 0x51, 0xdc, 0xfc, 0x9d, 
        0x15, 0x89, 0xa1, 0x59, 0x7e, 0x3a, 0x51, 0x20, 
        0xe1, 0xef, 0xd6, 0x31, 0xc6, 0x3e, 0x18, 0x35,

        0xca, 0xca, 0xe2, 0x98, 0x69, 0xa6, 0x2e, 0x16, 
        0x31, 0xe8, 0xa2, 0x81, 0x81, 0xab, 0x56, 0x61, 
        0x6d, 0xc4, 0x5d, 0x91, 0x8a, 0xbc, 0x09, 0xf3, 
        0xab, 0x0e, 0x63, 0xcf, 0x79, 0x2a, 0xa4, 0xdc, 
        0xed, 0x73, 0x87, 0xbe, 0x37, 0xbb, 0xa5, 0x69, 
        0x54, 0x9f, 0x1c, 0x02, 0xb2, 0x70, 0xed, 0x67
};

    printf("\n");
    printf("%s\n", "ECDH Initiator - P384 - Montgomery Ladder");


    uint8_t* result_p384 = (uint8_t*) malloc (sizeof (uint8_t) * 96);
    bool successDHI_p384 = Hacl_P256_ecp384dh_i_ml(result_p384, privateKey_p384);
    printf("\n");
    ok = ok && successDHI_p384;
    compare_and_print(48, result_p384, expectedPublicKeyX_p384);
    compare_and_print(48, result_p384 + 48, expectedPublicKeyY_p384);
    printf("\n");
    printf("%s\n", "---------------------------------------------------------------" );
    printf("\n");
    printf("%s\n", "ECDH Initiator - P384 - Radix");
    successDHI_p384 = Hacl_P256_ecp384dh_i_radix(result_p384, privateKey_p384);
    printf("\n");
    ok = ok && successDHI_p384;
    compare_and_print(48, result_p384, expectedPublicKeyX_p384);
    compare_and_print(48, result_p384 + 48, expectedPublicKeyY_p384);

    printf("\n");
    printf("%s\n", "---------------------------------------------------------------" );
    printf("\n");

    printf("%s\n", "ECDH Initiator - P384 - WNAF");
    successDHI_p384 = Hacl_P256_ecp384dh_i_wnaf(result_p384, privateKey_p384);
    printf("\n");
    ok = ok && successDHI_p384;
    compare_and_print(48, result_p384, expectedPublicKeyX_p384);
    compare_and_print(48, result_p384 + 48, expectedPublicKeyY_p384);

    printf("\n");
    printf("%s\n", "---------------------------------------------------------------" );
    printf("\n");

    printf("%s\n", "ECDH Responder - P384 - Montgomery Ladder");
    printf("\n");

    uint8_t* pk_p384 = (uint8_t*) malloc (sizeof (uint8_t) * 96);
    memcpy(pk_p384, expectedPublicKeyX_p384,  48);
    memcpy(pk_p384 + 48, expectedPublicKeyY_p384,  48);
       
    successDHR = Hacl_P256_ecp384dh_r_private_ml(result_p384, pk_p384, privateKey_p384);
    ok = ok && compare_and_print(48, result_p384, expectedResult_p384);
    ok = ok && compare_and_print(48, result_p384 + 48, expectedResult_p384 + 48);
    ok = ok && successDHR;

    printf("\n");
    printf("%s\n", "---------------------------------------------------------------" );
    printf("\n");
    printf("%s\n", "ECDH Responder - P384 - Radix");
    printf("\n");

    successDHR = Hacl_P256_ecp384dh_r_private_radix(result_p384, pk_p384, privateKey_p384);
    ok = ok && compare_and_print(48, result_p384, expectedResult_p384);
    ok = ok && compare_and_print(48, result_p384 + 48, expectedResult_p384 + 48);
    ok = ok && successDHR;



    return ok;
}



void master_branch_test()
{
	cycles a,b;
	clock_t t1,t2;
	uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 32);

	uint64_t len = SIZE;

	uint8_t scalar[SIZE];
	memset(scalar,'P',SIZE);
	
  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_i_wnaf(result, scalar);

	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_i_wnaf(result, scalar);
	
	b = cpucycles_end();
	
	t2 = clock();
	clock_t tdiff1 = t2 - t1;
	cycles cdiff1 = b - a;

	double time = (((double)tdiff1) / CLOCKS_PER_SEC);
	double nsigs = ((double)ROUNDS) / time;
	printf("HACL P-256 [SecretToPublic] PERF Ladder \n");
	printf("ECDH %8.2f mul/s\n",nsigs);

  	printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff1/ROUNDS);


    static uint8_t publicKeyX1[32] = {
    0x70, 0x0c, 0x48, 0xf7, 0x7f, 0x56, 0x58, 0x4c, 0x5c, 0xc6, 0x32, 0xca, 0x65, 0x64, 0x0d, 0xb9, 0x1b, 0x6b, 0xac, 0xce, 0x3a, 0x4d, 0xf6, 0xb4, 0x2c, 0xe7, 0xcc, 0x83, 0x88, 0x33, 0xd2, 0x87 
    };

    static uint8_t publicKeyY1[32] = {
    0xdb, 0x71, 0xe5, 0x09, 0xe3, 0xfd, 0x9b, 0x06, 0x0d, 0xdb, 0x20, 0xba, 0x5c, 0x51, 0xdc, 0xc5, 0x94, 0x8d, 0x46, 0xfb, 0xf6, 0x40, 0xdf, 0xe0, 0x44, 0x17, 0x82, 0xca, 0xb8, 0x5f, 0xa4, 0xac 
    };
    
    static uint8_t privateKey[32] = {
    0x7d, 0x7d, 0xc5, 0xf7, 0x1e, 0xb2, 0x9d, 0xda, 0xf8, 0x0d, 0x62, 0x14, 0x63, 0x2e, 0xea, 0xe0, 0x3d, 0x90, 0x58, 0xaf, 0x1f, 0xb6, 0xd2, 0x2e, 0xd8, 0x0b, 0xad, 0xb6, 0x2b, 0xc1, 0xa5, 0x34 
    };

    static uint8_t privateKey1[32] = {
    0x7d, 0x7d, 0xc5, 0xf7, 0x1e, 0xb2, 0x9d, 0xda, 0xf8, 0x0d, 0x62, 0x14, 0x63, 0x2e, 0xea, 0xe0, 0x3d, 0x90, 0x58, 0xaf, 0x1f, 0xb6, 0xd2, 0x2e, 0xd8, 0x0b, 0xad, 0xb6, 0x2b, 0xc1, 0xa5, 0x34 
    };


	uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* resultECDHR = (uint8_t*) malloc (sizeof (uint8_t) * 64);

	for (int j = 0; j < ROUNDS; j++) {
		successDHR = Hacl_P256_ecp256dh_r_private_radix(result, pk, privateKey);
	}

	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++) {
  		memcpy(pk, publicKeyX1,  32);
    	memcpy(pk + 32, publicKeyY1,  32);
		bool success = Hacl_P256_ecp256dh_r_private_radix(result, pk, privateKey);	
	}
	
	b = cpucycles_end();
	t2 = clock();

	clock_t tdiff2 = t2 - t1;

	double timeLadderR = (((double)tdiff2) / CLOCKS_PER_SEC);
	double nsigsLadderR = ((double)ROUNDS) / timeLadderR;
	printf("HACL P-256 ECDH [Scalar Multiplication] PERF Ladder \n");
	printf("ECDH %8.2f mul/s\n",nsigsLadderR);

	cycles cdiff6 = b - a;
  	printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff6/ROUNDS);

}

bool test_ecdsa()
{
    uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    bool ok = true;

    static uint8_t pkx_0  [32] = { 
    0x29, 0x27, 0xb1, 0x05, 0x12, 0xba, 0xe3, 0xed, 0xdc, 0xfe, 0x46, 0x78, 0x28, 0x12, 0x8b, 0xad, 0x29, 0x03, 0x26, 0x99, 0x19, 0xf7, 0x08, 0x60, 0x69, 0xc8, 0xc4, 0xdf, 0x6c, 0x73, 0x28, 0x38}; 

    static uint8_t pky_0  [32] = {
    0xc7, 0x78, 0x79, 0x64, 0xea, 0xac, 0x00, 0xe5, 0x92, 0x1f, 0xb1, 0x49, 0x8a, 0x60, 0xf4, 0x60, 0x67, 0x66, 0xb3, 0xd9, 0x68, 0x50, 0x01, 0x55, 0x8d, 0x1a, 0x97, 0x4e, 0x73, 0x41, 0x51, 0x3e};

    #define mLen0 6 

    static uint8_t msg_0  [6] = {
    0x31, 0x32, 0x33, 0x34, 0x30, 0x30
    }; 

    static uint8_t r_0  [32] = {
    0x2b, 0xa3, 0xa8, 0xbe, 0x6b, 0x94, 0xd5, 0xec, 0x80, 0xa6, 0xd9, 0xd1, 0x19, 0x0a, 0x43, 0x6e, 0xff, 0xe5, 0x0d, 0x85, 0xa1, 0xee, 0xe8, 0x59, 0xb8, 0xcc, 0x6a, 0xf9, 0xbd, 0x5c, 0x2e, 0x18
    }; 

    static uint8_t s_0  [32] = {
    0x4c, 0xd6, 0x0b, 0x85, 0x5d, 0x44, 0x2f, 0x5b, 0x3c, 0x7b, 0x11, 0xeb, 0x6c, 0x4e, 0x0a, 0xe7, 0x52, 0x5f, 0xe7, 0x10, 0xfa, 0xb9, 0xaa, 0x7c, 0x77, 0xa6, 0x7f, 0x79, 0xe6, 0xfa, 0xdd, 0x76
    }; 

    #define result___0 0

    memcpy(pk, pkx_0, 32);
    memcpy(pk + 32, pky_0, 32);


    bool verificationSuccessful = Hacl_P256_ecdsa_verif_p256_sha2(mLen0, msg_0, pk, r_0, s_0);    
    if (verificationSuccessful)  
     {
        printf("%s\n", "Verification success");
     ok = true;
     }
        else
    { 
         printf("%s\n", "Verification Failed");
        ok = false;

    }



    uint8_t
    prKey[32U] =
      {
        (uint8_t)81U, (uint8_t)155U, (uint8_t)66U, (uint8_t)61U, (uint8_t)113U, (uint8_t)95U,
        (uint8_t)139U, (uint8_t)88U, (uint8_t)31U, (uint8_t)79U, (uint8_t)168U, (uint8_t)238U,
        (uint8_t)89U, (uint8_t)244U, (uint8_t)119U, (uint8_t)26U, (uint8_t)91U, (uint8_t)68U,
        (uint8_t)200U, (uint8_t)19U, (uint8_t)11U, (uint8_t)78U, (uint8_t)62U, (uint8_t)172U,
        (uint8_t)202U, (uint8_t)84U, (uint8_t)165U, (uint8_t)109U, (uint8_t)218U, (uint8_t)114U,
        (uint8_t)180U, (uint8_t)100U
      };

    uint8_t
    digest[32U] =
      {
        (uint8_t)28U, (uint8_t)203U, (uint8_t)233U, (uint8_t)28U, (uint8_t)7U, (uint8_t)95U,
        (uint8_t)199U, (uint8_t)244U, (uint8_t)240U, (uint8_t)51U, (uint8_t)191U, (uint8_t)162U,
        (uint8_t)72U, (uint8_t)219U, (uint8_t)143U, (uint8_t)204U, (uint8_t)211U, (uint8_t)86U,
        (uint8_t)93U, (uint8_t)233U, (uint8_t)75U, (uint8_t)191U, (uint8_t)177U, (uint8_t)47U,
        (uint8_t)60U, (uint8_t)89U, (uint8_t)255U, (uint8_t)70U, (uint8_t)194U, (uint8_t)113U,
        (uint8_t)191U, (uint8_t)131U
      };

    uint8_t
    nonce[32U] =
      {
        (uint8_t)148U, (uint8_t)161U, (uint8_t)187U, (uint8_t)177U, (uint8_t)75U, (uint8_t)144U,
        (uint8_t)106U, (uint8_t)97U, (uint8_t)162U, (uint8_t)128U, (uint8_t)242U, (uint8_t)69U,
        (uint8_t)249U, (uint8_t)233U, (uint8_t)60U, (uint8_t)127U, (uint8_t)59U, (uint8_t)74U,
        (uint8_t)98U, (uint8_t)71U, (uint8_t)130U, (uint8_t)79U, (uint8_t)93U, (uint8_t)51U,
        (uint8_t)185U, (uint8_t)103U, (uint8_t)7U, (uint8_t)135U, (uint8_t)100U, (uint8_t)42U,
        (uint8_t)104U, (uint8_t)222U
      };

    uint8_t
    siggen_vectors_low5[32U] =
      {
        (uint8_t)243U, (uint8_t)172U, (uint8_t)128U, (uint8_t)97U, (uint8_t)181U, (uint8_t)20U,
        (uint8_t)121U, (uint8_t)91U, (uint8_t)136U, (uint8_t)67U, (uint8_t)227U, (uint8_t)214U,
        (uint8_t)98U, (uint8_t)149U, (uint8_t)39U, (uint8_t)237U, (uint8_t)42U, (uint8_t)253U,
        (uint8_t)107U, (uint8_t)31U, (uint8_t)106U, (uint8_t)85U, (uint8_t)90U, (uint8_t)122U,
        (uint8_t)202U, (uint8_t)187U, (uint8_t)94U, (uint8_t)111U, (uint8_t)121U, (uint8_t)200U,
        (uint8_t)194U, (uint8_t)172U
      };

    uint8_t
    siggen_vectors_low6[32U] =
      {
        0xcf, 0xa7, 0x40, 0xfe, 0xc7, 0x67, 0x96, 0xd2, 
        0xe3, 0x92, 0x16, 0xbe, 0x7e, 0xbf, 0x58, 0x0e, 
        0xa3, 0xc0, 0xef, 0x4b, 0xb0, 0x0a, 0xb2, 0xe7, 
        0xe4, 0x20, 0x84, 0x34, 0xf4, 0x5f, 0x8c, 0x9c
      };


    static uint8_t px0_0[32] = {
    0x70, 0x0c, 0x48, 0xf7, 0x7f, 0x56, 0x58, 0x4c, 0x5c, 0xc6, 0x32, 0xca, 0x65, 0x64, 0x0d, 0xb9, 0x1b, 0x6b, 0xac, 0xce, 0x3a, 0x4d, 0xf6, 0xb4, 0x2c, 0xe7, 0xcc, 0x83, 0x88, 0x33, 0xd2, 0x87 

    };
    static uint8_t py0_0[32] = {
    0xdb, 0x71, 0xe5, 0x09, 0xe3, 0xfd, 0x9b, 0x06, 0x0d, 0xdb, 0x20, 0xba, 0x5c, 0x51, 0xdc, 0xc5, 0x94, 0x8d, 0x46, 0xfb, 0xf6, 0x40, 0xdf, 0xe0, 0x44, 0x17, 0x82, 0xca, 0xb8, 0x5f, 0xa4, 0xac 
    };

    static uint8_t scalar0[32] = {
    0x7d, 0x7d, 0xc5, 0xf7, 0x1e, 0xb2, 0x9d, 0xda, 0xf8, 0x0d, 0x62, 0x14, 0x63, 0x2e, 0xea, 0xe0, 0x3d, 0x90, 0x58, 0xaf, 0x1f, 0xb6, 0xd2, 0x2e, 0xd8, 0x0b, 0xad, 0xb6, 0x2b, 0xc1, 0xa5, 0x34 

    };





    uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    bool flag = Hacl_P256_ecdsa_sign_p256_without_hash(result, 32, digest, prKey, nonce);
    bool s0 = compare_and_print(32, result, siggen_vectors_low5);
    bool s1 = compare_and_print(32, result + 32, siggen_vectors_low6);

    return ok && s0 && s1 && flag;
}






int main()
{

    if (test_ecdh () == false)
        printf("%s\n", "WRONG"); 
    if (test_ecdsa () == false)
        printf("%s\n", "WRONG"); 


	master_branch_test();
}

// #include <inttypes.h>
// void printU(uint64_t* t, int len)
// {
//   for (int i = 0; i< len; i++) {
//     printf("%016llX ", t[i]);  
//   }
//   printf("\n");
// }