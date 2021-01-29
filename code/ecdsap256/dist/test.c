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
// #include "Hacl_P256_first_version.h"
#include "fiat.c"



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


void hex2bytes(unsigned char *out, const char *in) {
    int i;
    int len = strlen(in);

    assert(out != NULL);
    assert(in != NULL);
    assert(len == 64);

    for (i = len - 2; i >= 0; i -= 2, out++)
        assert(sscanf(in + i, "%02hhx", out) == 1);
}


#define MP_BE2LE(a)            \
    do {                       \
        unsigned char z_bswap; \
        z_bswap = a[0];        \
        a[0] = a[31];          \
        a[31] = z_bswap;       \
        z_bswap = a[1];        \
        a[1] = a[30];          \
        a[30] = z_bswap;       \
        z_bswap = a[2];        \
        a[2] = a[29];          \
        a[29] = z_bswap;       \
        z_bswap = a[3];        \
        a[3] = a[28];          \
        a[28] = z_bswap;       \
        z_bswap = a[4];        \
        a[4] = a[27];          \
        a[27] = z_bswap;       \
        z_bswap = a[5];        \
        a[5] = a[26];          \
        a[26] = z_bswap;       \
        z_bswap = a[6];        \
        a[6] = a[25];          \
        a[25] = z_bswap;       \
        z_bswap = a[7];        \
        a[7] = a[24];          \
        a[24] = z_bswap;       \
        z_bswap = a[8];        \
        a[8] = a[23];          \
        a[23] = z_bswap;       \
        z_bswap = a[9];        \
        a[9] = a[22];          \
        a[22] = z_bswap;       \
        z_bswap = a[10];       \
        a[10] = a[21];         \
        a[21] = z_bswap;       \
        z_bswap = a[11];       \
        a[11] = a[20];         \
        a[20] = z_bswap;       \
        z_bswap = a[12];       \
        a[12] = a[19];         \
        a[19] = z_bswap;       \
        z_bswap = a[13];       \
        a[13] = a[18];         \
        a[18] = z_bswap;       \
        z_bswap = a[14];       \
        a[14] = a[17];         \
        a[17] = z_bswap;       \
        z_bswap = a[15];       \
        a[15] = a[16];         \
        a[16] = z_bswap;       \
    } while (0)



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

	printf("%s\n", "ECDH Initiator");



	uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	
	
	bool successDHI = Hacl_P256_ecp256dh_i_ladder(result, privateKey);
	printf("\n");
	ok = ok && successDHI;
	ok = ok && compare(32, result, expectedPublicKeyX);
	ok = ok && compare(32, result + 32, expectedPublicKeyY);

	bool successDHI_Radix = Hacl_P256_ecp256dh_i_radix4(result, privateKey);
	ok = ok && successDHI_Radix;
	ok = ok && compare(32, result, expectedPublicKeyX);
	ok = ok && compare(32, result + 32, expectedPublicKeyY);


	bool successDHI_Comb = Hacl_P256_ecp256dh_i_cmb(result, privateKey);
	ok = ok && compare_and_print(32, result, expectedPublicKeyX);
	ok = ok && compare_and_print(32, result + 32, expectedPublicKeyY);


	printf("\n");

	printf("%s\n", "---------------------------------------------------------------" );

	printf("%s\n", "ECDH Responder");


	result = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	memcpy(pk, publicKeyX1,  32);
	memcpy(pk+32, publicKeyY1,  32);
	   
	// bool successDHR = Hacl_P256_ecp256dh_r_ladder(result, pk, privateKey);
	// ok = ok && successDHR;
	// ok = ok && compare_and_print(32, result, expectedResult);


	bool successDHR_Radix = Hacl_P256_ecp256dh_r_radix4(result, pk, privateKey);
	ok = ok && successDHR_Radix;
	ok = ok && compare_and_print(32, result, expectedResult);

	// bool successDHR_Comb = Hacl_P256_ecp256dh_r_comb(result, pk, privateKey);
	// compare_and_print(32, result, expectedResult);


	printf("\n");

	printf("%s\n", "---------------------------------------------------------------" );

	printf("%s\n", "External code testing");

	uint8_t* outx = (uint8_t*) malloc (sizeof (uint8_t) * 32);
	uint8_t* outy = (uint8_t*) malloc (sizeof (uint8_t) * 32);


	MP_BE2LE(privateKey);

	point_mul_g(outx, outy, privateKey);

	MP_BE2LE(outx);
	MP_BE2LE(outy);

	ok = ok && compare_and_print(32, outx, expectedPublicKeyX);
	ok = ok && compare_and_print(32, outy, expectedPublicKeyY);




	MP_BE2LE(publicKeyX1);
	MP_BE2LE(publicKeyY1);

	point_mul(outx, outy, privateKey, publicKeyX1, publicKeyY1);

	MP_BE2LE(outx);
	MP_BE2LE(outy);

	ok = ok && compare_and_print(32, outx, expectedResult);

	free(result);
	free(pk);


	return ok;
}


bool test_ecdsa()
{

	uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	bool ok;

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


	bool verificationSuccessful = Hacl_P256_ecdsa_verif_p256_sha2_comb_radix(mLen0, msg_0, pk, r_0, s_0);	
	if (verificationSuccessful)	
		ok = true;
	else
		ok = false;

	return ok;


}


int main()
{



	if (test_ecdh())
		printf("%s\n", "ECDH Testing is correct \n ");
	else
		{
			printf("%s\n", "ECDH Testing is failed \n ");
			return -1;
		}

	if (test_ecdsa())
		printf("%s\n", "ECDSA Testing is correct \n ");
	else
		{
			printf("%s\n", "ECDSA Testing is failed \n ");
			return -1;
		}


	// return -1;


	cycles a,b;
	clock_t t1,t2;
	uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 32);

	uint64_t len = SIZE;

	uint8_t scalar[SIZE];
	memset(scalar,'P',SIZE);
	
  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_i_ladder(result, scalar);

	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_i_ladder(result, scalar);
	
	b = cpucycles_end();
	
	t2 = clock();
	clock_t tdiff1 = t2 - t1;
	cycles cdiff1 = b - a;

	double time = (((double)tdiff1) / CLOCKS_PER_SEC);
	double nsigs = ((double)ROUNDS) / time;
	printf("HACL P-256 [SecretToPublic] PERF Ladder \n");
	printf("ECDH %8.2f mul/s\n",nsigs);

  	printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff1/ROUNDS);







  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_i_radix4(result, scalar);

	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_i_radix4(result, scalar);
	
	b = cpucycles_end();
	
	t2 = clock();
	clock_t tdiff2 = t2 - t1;
	cycles cdiff2 = b - a;

	double timeRadix = (((double)tdiff2) / CLOCKS_PER_SEC);
	double nsigsRadix = ((double)ROUNDS) / timeRadix;
	printf("HACL P-256 ECDH [SecretToPublic] PERF Radix4 \n");
	printf("ECDH %8.2f mul/s\n",nsigsRadix);

  	printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff2/ROUNDS);








  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_i_cmb(result, scalar);

	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_i_cmb(result, scalar);
	
	b = cpucycles_end();
	
	t2 = clock();
	clock_t tdiff5 = t2 - t1;
	cycles cdiff3 = b - a;

	double timeComb = (((double)tdiff5) / CLOCKS_PER_SEC);
	double nsigsComb= ((double)ROUNDS) / timeComb;
	printf("HACL P-256 ECDH [SecretToPublic] PERF Comb \n");
	printf("ECDH %8.2f mul/s\n",nsigsComb);
	printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff3/ROUNDS);






	printf("%s\n", "-----------------------------------------------------");


 //  	for (int j = 0; j < ROUNDS; j++)
	// 	Hacl_P256_ecp256dh_i(result, scalar);

	// t1 = clock();
 //  	a = cpucycles_begin();

 //  	for (int j = 0; j < ROUNDS; j++)
	// 	Hacl_P256_ecp256dh_i(result, scalar);
	
	// b = cpucycles_end();
	
	// t2 = clock();
	// clock_t tdiff3 = t2 - t1;
	// cycles cdiff4 = b - a;

	// double timeFirstVersion = (((double)tdiff3) / CLOCKS_PER_SEC);
	// double nsigsFirstVersion = ((double)ROUNDS) / timeFirstVersion;
	// printf("HACL P-256 ECDH PERF [SecretToPublic] Initial version \n");
	// printf("ECDH %8.2f mul/s\n",nsigsFirstVersion);
 //  	printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff4/ROUNDS);





	printf("%s\n", "----------------------------------------------------");


	uint8_t* outx = (uint8_t*) malloc (sizeof (uint8_t) * 32);
	uint8_t* outy = (uint8_t*) malloc (sizeof (uint8_t) * 32);


  	for (int j = 0; j < ROUNDS; j++)
		point_mul_g(outx, outy, scalar);

	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
		point_mul_g(outx, outy, scalar);
	
	b = cpucycles_end();
	
	t2 = clock();
	clock_t tdiff4 = t2 - t1;
	cycles cdiff5 = b - a;

	double timeFiat = (((double)tdiff4) / CLOCKS_PER_SEC);
	double nsigsFiat = ((double)ROUNDS) / timeFiat;
	printf("EccKilla P-256 ECDH [SecretToPublic] PERF \n");
	printf("ECDH %8.2f mul/s\n",nsigsFiat);
  	printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff5/ROUNDS);

	
	printf("%s\n", "----------------------------------------------------");


	static uint8_t publicKeyX1[32] = {
	0x70, 0x0c, 0x48, 0xf7, 0x7f, 0x56, 0x58, 0x4c, 0x5c, 0xc6, 0x32, 0xca, 0x65, 0x64, 0x0d, 0xb9, 0x1b, 0x6b, 0xac, 0xce, 0x3a, 0x4d, 0xf6, 0xb4, 0x2c, 0xe7, 0xcc, 0x83, 0x88, 0x33, 0xd2, 0x87 

	};
	static uint8_t publicKeyY1[32] = {
	0xdb, 0x71, 0xe5, 0x09, 0xe3, 0xfd, 0x9b, 0x06, 0x0d, 0xdb, 0x20, 0xba, 0x5c, 0x51, 0xdc, 0xc5, 0x94, 0x8d, 0x46, 0xfb, 0xf6, 0x40, 0xdf, 0xe0, 0x44, 0x17, 0x82, 0xca, 0xb8, 0x5f, 0xa4, 0xac 

	};
	static uint8_t privateKey[32] = {
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


	uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	
	memcpy(pk, publicKeyX1,  32);
	memcpy(pk+32, publicKeyY1,  32);

	  for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_r_radix4(result, pk, privateKey);


	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_r_radix4(result, pk, privateKey);
	
	b = cpucycles_end();
	
	t2 = clock();
	clock_t tdiff6 = t2 - t1;

	double timeLadderR = (((double)tdiff6) / CLOCKS_PER_SEC);
	double nsigsLadderR = ((double)ROUNDS) / timeLadderR;
	printf("HACL P-256 ECDH [Scalar Multiplication] PERF Radix4 \n");
	printf("ECDH %8.2f mul/s\n",nsigsLadderR);

	cycles cdiff6 = b - a;
  	printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff6/ROUNDS);






	memcpy(pk, publicKeyX1,  32);
	memcpy(pk+32, publicKeyY1,  32);

	  for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_r_ladder(result, pk, privateKey);


	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_r_ladder(result, pk, privateKey);
	
	b = cpucycles_end();
	
	t2 = clock();
	clock_t tdiff_r_ladder = t2 - t1;

	double timeLadderRE = (((double)tdiff_r_ladder) / CLOCKS_PER_SEC);
	double nsigsLadderRE = ((double)ROUNDS) / timeLadderRE;
	printf("HACL P-256 ECDH [Scalar Multiplication] PERF Ladder \n");
	printf("ECDH %8.2f mul/s\n",nsigsLadderRE);

	cycles cdiff7 = b - a;
  	printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff7/ROUNDS);







	// pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	
	// memcpy(pk, publicKeyX1,  32);
	// memcpy(pk+32, publicKeyY1,  32);

	//   for (int j = 0; j < ROUNDS; j++)
	// 	Hacl_P256_ecp256dh_r_comb(result, pk, privateKey);


	// t1 = clock();
 //  	a = cpucycles_begin();

 //  	for (int j = 0; j < ROUNDS; j++)
	// 	Hacl_P256_ecp256dh_r_comb(result, pk, privateKey);
	
	// b = cpucycles_end();
	
	// t2 = clock();
	// clock_t tdiff_r_comb = t2 - t1;

	// double timeRComb = (((double)tdiff_r_comb) / CLOCKS_PER_SEC);
	// double nsigsRComb = ((double)ROUNDS) / timeRComb;
	// printf("HACL P-256 ECDH [Scalar Multiplication] PERF WNAF \n NB: The computation (only of this piece of code) is incorrect, put just for comparision. I don't expect a huge change \n");
	// printf("ECDH %8.2f mul/s\n",nsigsRComb);

	// cycles cdiff8 = b - a;
 //  	printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff8/ROUNDS);






  	for (int j = 0; j < ROUNDS; j++)
		point_mul(outx, outy, privateKey, publicKeyX1, publicKeyY1);

	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
		point_mul(outx, outy, privateKey, publicKeyX1, publicKeyY1);
	
	b = cpucycles_end();
	
	t2 = clock();
	clock_t tdiff7 = t2 - t1;

	double timeECCKillaR = (((double)tdiff7) / CLOCKS_PER_SEC);
	double nsigsECCKillaR = ((double)ROUNDS) / timeECCKillaR;
	printf("ECC Killa P-256 ECDH [Scalar Multiplication] PERF \n");
	printf("ECDH %8.2f mul/s\n",nsigsECCKillaR);

	cycles cdiff9 = b - a;
  	printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff9/ROUNDS);




	printf("%s\n", "----------------------------------------------------");
	printf("%s\n", "----------------------------------------------------");
	printf("%s\n", "----------------------------------------------------");


	uint8_t* pk_ecdsa = (uint8_t*) malloc (sizeof (uint8_t) * 100);
	bool ok;

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

	memcpy(pk_ecdsa, pkx_0, 32);
	memcpy(pk_ecdsa + 32, pky_0, 32);


	bool verificationSuccessful = true;

  	for (int j = 0; j < ROUNDS; j++)
		verificationSuccessful = Hacl_P256_ecdsa_verif_p256_sha2_comb_radix(mLen0, msg_0, pk_ecdsa, r_0, s_0);	

	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
		verificationSuccessful = Hacl_P256_ecdsa_verif_p256_sha2_comb_radix(mLen0, msg_0, pk_ecdsa, r_0, s_0);
	
	b = cpucycles_end();
	
	t2 = clock();
	clock_t tdiff_ecdsa = t2 - t1;

	double time_ecdsa_verification_ladder = (((double)tdiff_ecdsa) / CLOCKS_PER_SEC);
	double nsigs_ecdsa_verification_ladder = ((double)ROUNDS) / time_ecdsa_verification_ladder;
	printf("Hacl P-256 ECDSA Verification PERF Ladder\n");
	printf("ECDH %8.2f mul/s\n",nsigs_ecdsa_verification_ladder);

	cycles cdiff10 = b - a;
  	printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff10/ROUNDS);





	uint8_t* result_ecdsa = (uint8_t*) malloc (sizeof (uint8_t) * 32);
	bool signSuccessful = true;

  	for (int j = 0; j < ROUNDS; j++)
		signSuccessful = Hacl_P256_ecdsa_sign_p256_sha2_comb(result_ecdsa, mLen0, msg_0,  r_0, s_0);	

	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
		signSuccessful = Hacl_P256_ecdsa_sign_p256_sha2_comb(result_ecdsa, mLen0, msg_0, r_0, s_0);
	
	b = cpucycles_end();
	
	t2 = clock();
	clock_t tdiff_ecdsa_s = t2 - t1;

	double time_ecdsa_signature_ladder = (((double)tdiff_ecdsa_s) / CLOCKS_PER_SEC);
	double nsigs_ecdsa_signature_ladder = ((double)ROUNDS) / time_ecdsa_signature_ladder;
	printf("Hacl P-256 ECDSA Signature PERF Ladder\n");
	printf("ECDH %8.2f mul/s\n",nsigs_ecdsa_signature_ladder);

	cycles cdiff11 = b - a;
  	printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff11/ROUNDS);












}

// #include <inttypes.h>
// void printU(uint64_t* t, int len)
// {
//   for (int i = 0; i< len; i++) {
//     printf("%016llX ", t[i]);  
//   }
//   printf("\n");
// }
