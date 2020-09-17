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
		bool success = Hacl_P256_ecp256dh_i(result, i_vectors[i].privateKey);
		ok = ok && success;
		ok = ok && compare_and_print(32, result, i_vectors[i].expectedPublicKeyX);
		ok = ok && compare_and_print(32, result + 32, i_vectors[i].expectedPublicKeyY);
	}


	printf("%s\n", "ECDH Responder tests: \n");
	
	for (int i = 0 ; i< sizeof(i_vectors)/sizeof(ecdhp256_tv_i); i++)
	{

		printf("ECDH Responder Test %d\n", i );
		memcpy(pk, i_vectors[i].publicKeyX1,  32);
		memcpy(pk+32, i_vectors[i].publicKeyY1,  32);
	   
	    bool success = Hacl_P256_ecp256dh_r(result, pk, i_vectors[i].privateKey);
	    ok = ok && success;
	    ok = ok && compare_and_print(32, result, i_vectors[i].expectedResult);
	}


	free(result);
	free(pk);

	return ok;
}


bool test_compression()
{
	// The start of compression tests
	printf("Compression function test\n");
	bool ok = true;

	static uint8_t point_compressed[64] = {
	0x70, 0x0c, 0x48, 0xf7, 0x7f, 0x56, 0x58, 0x4c, 
	0x5c, 0xc6, 0x32, 0xca, 0x65, 0x64, 0x0d, 0xb9, 
	0x1b, 0x6b, 0xac, 0xce, 0x3a, 0x4d, 0xf6, 0xb4, 
	0x2c, 0xe7, 0xcc, 0x83, 0x88, 0x33, 0xd2, 0x87, 
	0xdb, 0x71, 0xe5, 0x09, 0xe3, 0xfd, 0x9b, 0x06, 
	0x0d, 0xdb, 0x20, 0xba, 0x5c, 0x51, 0xdc, 0xc5, 
	0x94, 0x8d, 0x46, 0xfb, 0xf6, 0x40, 0xdf, 0xe0, 
	0x44, 0x17, 0x82, 0xca, 0xb8, 0x5f, 0xa4, 0xac};

	uint8_t* compressed0 = (uint8_t *) malloc (sizeof (uint8_t) * 65);
	uint8_t* compressed1 = (uint8_t *) malloc (sizeof (uint8_t) * 64);
	uint8_t* compressed2 = (uint8_t *) malloc (sizeof (uint8_t) * 65);
	uint8_t* compressed3 = (uint8_t *) malloc (sizeof (uint8_t) * 64);

	Hacl_P256_compression_not_compressed_form(point_compressed, compressed0);
	Hacl_P256_decompression_not_compressed_form(compressed0, compressed1);
	Hacl_P256_compression_not_compressed_form(compressed1, compressed2);
	Hacl_P256_decompression_not_compressed_form(compressed2, compressed3);

	ok = ok && compare_and_print(64, point_compressed, compressed3);


	printf("Compression function test2\n");

	uint8_t* compressed4 = (uint8_t *) malloc (sizeof (uint8_t) * 33);
	uint8_t* compressed5 = (uint8_t *) malloc (sizeof (uint8_t) * 64);
	uint8_t* compressed6 = (uint8_t *) malloc (sizeof (uint8_t) * 33);
	uint8_t* compressed7 = (uint8_t *) malloc (sizeof (uint8_t) * 64);


	Hacl_P256_compression_compressed_form(point_compressed, compressed4);
	Hacl_P256_decompression_compressed_form(compressed4, compressed5);
	Hacl_P256_compression_compressed_form(compressed5, compressed6);
	Hacl_P256_decompression_compressed_form(compressed6, compressed7);

	ok = ok && compare_and_print(64, point_compressed, compressed7);

	free(compressed0);
	free(compressed1);
	free(compressed2);
	free(compressed3);
	free(compressed4);
	free(compressed5);
	free(compressed6);
	free(compressed7);

	return ok;

}


bool test_wycheproof()
{

	uint8_t* decompressedPoint = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);

	bool ok = true;

	printf("%s\n", "Wycheproof tests ECDH: ");
		
	for (int i = 0 ; i< sizeof(w_vectors)/sizeof(ecdhp256_w_i); i++)
	{
		printf("ECDH Wycheproof Test %d \n", i );

		bool flagDecompressSuccessful = Hacl_P256_decompression_not_compressed_form(w_vectors[i].publicKey, decompressedPoint);
		bool success = Hacl_P256_ecp256dh_r(result, decompressedPoint, w_vectors[i].privateKey);
		
		if (w_vectors[i].flag != 1) 
		{
			// We start with the check that the point was decompressed successfully and that the execution of the dh_r function was successul. 
			// If one of them has failed, we consider the result of the test to be false. This result is further compared with the expected flag.
			// If the execution was correct, we also check the results. 

			if (!flagDecompressSuccessful)
				success = false;

			// if the flag that the test returns states that the execution was INCORRECT but the flag we got is opposite - we consider the test to fail

			if ((w_vectors[i].flag == incorrect) && success)
				ok = false;

			f ((w_vectors[i].flag == correct) && !success)
				ok = false;

			if (success) 
				ok = ok && compare_and_print(32, result, w_vectors[i].sharedKey);
		}
		else
			if (success)
				ok = ok && compare_and_print(32, result, w_vectors[i].sharedKey);

		if (!ok) 
			{
				printf("Test %d \n failed", i);
				break;
			}
	}


	printf("%s\n", "Wycheproof tests ECDSA: ");
		
	for (int i = 0 ; i< sizeof(w_ecdsa_vectors)/sizeof(ecdsap256_w_i) ; i++)
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
	
	return ok; 
}


int main()
{

  if (!test_nist())
    return EXIT_FAILURE;
  if (!test_compression())
    return EXIT_FAILURE;
  if (!test_wycheproof())
    return EXIT_FAILURE;
  return EXIT_SUCCESS;
}
