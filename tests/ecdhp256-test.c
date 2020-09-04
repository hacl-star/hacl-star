#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>
#include <time.h>

#include "ecdhp256-tvs.h"
#include "ecdhp256_tv_w.h"
#include "ecdsap256_tv_w.h"

#include "test_helpers.h"
#include <inttypes.h>

#include "Hacl_P256.h"


uint64_t incorrect = UINT64_MAX;
uint64_t correct = 0;

bool test_nist()
{

	uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	
	bool ok = true;


	printf("%s\n", "ECDH Initiator tests: \n");

	for (int i = 0 ; i< sizeof(i_vectors)/sizeof(ecdhp256_tv_i); i++)
	{
		printf("ECDH Initiator Test %d \n", i );
		uint64_t success = Hacl_P256_ecp256dh_i(result, i_vectors[i].privateKey);
		ok = ok && (success == 0);
		ok = ok && compare_and_print(32, result, i_vectors[i].expectedPublicKeyX);
		ok = ok && compare_and_print(32, result + 32, i_vectors[i].expectedPublicKeyY);
	}


	printf("%s\n", "ECDH Responder tests: \n");
	
	for (int i = 0 ; i< sizeof(i_vectors)/sizeof(ecdhp256_tv_i); i++)
	{

		printf("ECDH Responder Test %d\n", i );
		memcpy(pk, i_vectors[i].publicKeyX1,  32);
		memcpy(pk+32, i_vectors[i].publicKeyY1,  32);
	   
	    uint64_t success = Hacl_P256_ecp256dh_r(result, pk, i_vectors[i].privateKey);
	    ok = ok && (success == 0);
	    ok = ok && compare_and_print(32, result, i_vectors[i].expectedResult);
	}


	free(result);
	free(pk);

	return ok;
}


// bool test_compression()
// {
// 	// The start of compression tests
// 	printf("Compression function test\n");
// 	bool ok = true;

// 	static uint8_t point_compressed[64] = {
// 	0x70, 0x0c, 0x48, 0xf7, 0x7f, 0x56, 0x58, 0x4c, 
// 	0x5c, 0xc6, 0x32, 0xca, 0x65, 0x64, 0x0d, 0xb9, 
// 	0x1b, 0x6b, 0xac, 0xce, 0x3a, 0x4d, 0xf6, 0xb4, 
// 	0x2c, 0xe7, 0xcc, 0x83, 0x88, 0x33, 0xd2, 0x87, 
// 	0xdb, 0x71, 0xe5, 0x09, 0xe3, 0xfd, 0x9b, 0x06, 
// 	0x0d, 0xdb, 0x20, 0xba, 0x5c, 0x51, 0xdc, 0xc5, 
// 	0x94, 0x8d, 0x46, 0xfb, 0xf6, 0x40, 0xdf, 0xe0, 
// 	0x44, 0x17, 0x82, 0xca, 0xb8, 0x5f, 0xa4, 0xac};

// 	uint8_t* compressed0 = (uint8_t *) malloc (sizeof (uint8_t) * 65);
// 	uint8_t* compressed1 = (uint8_t *) malloc (sizeof (uint8_t) * 64);
// 	uint8_t* compressed2 = (uint8_t *) malloc (sizeof (uint8_t) * 65);
// 	uint8_t* compressed3 = (uint8_t *) malloc (sizeof (uint8_t) * 64);

// 	Hacl_P256_compression_not_compressed_form(point_compressed, compressed0);
// 	Hacl_P256_decompression_not_compressed_form(compressed0, compressed1);
// 	Hacl_P256_compression_not_compressed_form(compressed1, compressed2);
// 	Hacl_P256_decompression_not_compressed_form(compressed2, compressed3);

// 	ok = ok && compare_and_print(64, point_compressed, compressed3);


// 	printf("Compression function test2\n");

// 	uint8_t* compressed4 = (uint8_t *) malloc (sizeof (uint8_t) * 33);
// 	uint8_t* compressed5 = (uint8_t *) malloc (sizeof (uint8_t) * 64);
// 	uint8_t* compressed6 = (uint8_t *) malloc (sizeof (uint8_t) * 33);
// 	uint8_t* compressed7 = (uint8_t *) malloc (sizeof (uint8_t) * 64);


// 	Hacl_P256_compression_compressed_form(point_compressed, compressed4);
// 	Hacl_P256_decompression_compressed_form(compressed4, compressed5);
// 	Hacl_P256_compression_compressed_form(compressed5, compressed6);
// 	Hacl_P256_decompression_compressed_form(compressed6, compressed7);

// 	ok = ok && compare_and_print(64, point_compressed, compressed7);

// 	free(compressed0);
// 	free(compressed1);
// 	free(compressed2);
// 	free(compressed3);
// 	free(compressed4);
// 	free(compressed5);
// 	free(compressed6);
// 	free(compressed7);

// 	return ok;

// }


bool test_wycheproof()
{

	uint8_t* decompressedPoint = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);

	bool ok = true;

	// printf("%s\n", "Wycheproof tests ECDH: ");
		
	// for (int i = 0 ; i< sizeof(w_vectors)/sizeof(ecdhp256_w_i); i++)
	// {
	// 	printf("ECDH Wycheproof Test %d \n", i );

	// 	bool flagDecompressSuccessful = Hacl_P256_decompression_not_compressed_form(w_vectors[i].publicKey, decompressedPoint);
	// 	uint64_t success = Hacl_P256_ecp256dh_r(result, decompressedPoint, w_vectors[i].privateKey);
		
	// 	if (w_vectors[i].flag != 1) 
	// 	{
	// 		// We start with the check that the point was decompressed successfully and that the execution of the dh_r function was successul. 
	// 		// If one of them has failed, we consider the result of the test to be false. This result is further compared with the expected flag.
	// 		// If the execution was correct, we also check the results. 

	// 		if (!flagDecompressSuccessful)
	// 			success = incorrect;

	// 		ok = ok && (success == w_vectors[i].flag);
	// 		if (success == 0) 
	// 			ok = ok && compare_and_print(32, result, w_vectors[i].sharedKey);
	// 	}
	// 	else
	// 		if (success == 0)
	// 			ok = ok && compare_and_print(32, result, w_vectors[i].sharedKey);

	// 	if (!ok) 
	// 		{
	// 			printf("Test %d \n failed", i);
	// 			break;
	// 		}
	// }


	printf("%s\n", "Wycheproof tests ECDSA: ");
		
	// for (int i = 0 ; i< sizeof(w_ecdsa_vectors)/sizeof(ecdsap256_w_i) ; i++)
	for (int i = 0 ; i< 10 ; i++)
	{
		printf("ECDSA Wycheproof Test %d \n", i );
		
		uint32_t mLen = w_ecdsa_vectors[i].mLen;

		memcpy(pk, w_ecdsa_vectors[i].publicX, 32);
		memcpy(pk + 32, w_ecdsa_vectors[i].publicY, 32);

		bool verificationSuccessful = Hacl_P256_ecdsa_verif_p256_sha2(mLen, w_ecdsa_vectors[i].message, pk, w_ecdsa_vectors[i].r, w_ecdsa_vectors[i].s);	
		
		if (w_ecdsa_vectors[i].flag == incorrect && verificationSuccessful)
		{
			ok = false;
		}	
		if (w_ecdsa_vectors[i].flag == correct && !verificationSuccessful)
		{
			ok = false;
		}


		if (!ok) 
		{
			printf("\n Test %d failed \n", i);
			compare_and_print(32, w_ecdsa_vectors[i].r, w_ecdsa_vectors[i].r);
			compare_and_print(32, w_ecdsa_vectors[i].s, w_ecdsa_vectors[i].s);
			break;
		}
	}

	free(decompressedPoint);
	free(result);
	free(pk);
}


int main()
{


// val ecp384dh_i:
//     result:lbuffer uint8 (size 96)
//   -> scalar:lbuffer uint8 (size 48)
//   -> Stack uint64

	uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 96);
	uint8_t expectedX[48] = {
		0x8D, 0x48, 0x1D, 0xAB, 0x91, 0x2B, 0xC8, 0xAB,
		0x16, 0x85, 0x8A, 0x21, 0x1D, 0x75, 0x0B, 0x77,
		0xE0, 0x7D, 0xBE, 0xCC, 0xA8, 0x6C, 0xD9, 0xB0,
		0x12, 0x39, 0x0B, 0x43, 0x04, 0x67, 0xAA, 0xBF,
		0x59, 0xC8, 0x65, 0x10, 0x60, 0x80, 0x1C, 0x0E,
		0x95, 0x99, 0xE6, 0x87, 0x13, 0xF5, 0xD4, 0x1B
	};

	uint8_t expectedY[48] = {
		0x5E, 0xA6, 0xD0, 0x0F, 0xED, 0xEB, 0x9F, 0x7A, 
		0x84, 0x16, 0x60, 0xD5, 0x9F, 0x99, 0x6F, 0xAF, 
		0x4D, 0xD6, 0xE4, 0x97, 0x5E, 0xFC, 0x65, 0x5F, 
		0xA6, 0xB4, 0xCD, 0x02, 0x85, 0x23, 0xF1, 0x72, 
		0xEE, 0x00, 0x45, 0xA8, 0xF7, 0xFF, 0xB1, 0x9B, 
		0x96, 0x6A, 0x4F, 0x82, 0x8A, 0x1A, 0xDD, 0xBA
	};


	// uint8_t scalar[48] = {
	// 	255, 255, 255, 255, 255, 255, 255, 255, 
	// 	255, 255, 255, 255, 255, 255, 255, 255, 
	// 	255, 255, 255, 255, 255, 255, 255, 255,
	// 	199, 99,  77,  129, 244,  55,  45, 223,
	// 	88,  26,  13,  178,  72, 176, 167, 122,
	// 	236, 236,  25, 106, 204, 197, 41,  96
	// };


	uint8_t* scalar = (uint8_t*) malloc (sizeof (uint8_t) * 48);

	uint8_t scalar1[48] = {
		0, 0, 0, 0, 0, 0, 0, 0, 
		0, 0, 0, 0, 0, 0, 0, 0, 
		0, 0, 0, 0, 0, 0, 0, 0, 
		0, 0, 0, 0, 0, 0, 0, 0, 
		0, 0, 0, 0, 0, 0, 0, 0, 
		0, 0, 0, 0, 0, 0, 0, 2
	};

	uint64_t success = Hacl_P256_ecp384dh_i(result, scalar1);	
	
	compare_and_print(48, result, expectedX);
	compare_and_print(48, result + 48, expectedY);








  // if (!test_nist())
  //   return EXIT_FAILURE;
  // // if (!test_compression())
  // //   return EXIT_FAILURE;
  // if (!test_wycheproof())
  //   return EXIT_FAILURE;
  // return EXIT_SUCCESS;
}
