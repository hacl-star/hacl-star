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

#include "ecdhp256-tvs.h"
#include "ecdhp256_tv_w.h"
#include "ecdsap256_tv_w.h"

#include "test_helpers.h"
#include <inttypes.h>

#include "Hacl_P256.h"


static uint8_t point_compressed[64] = {
	0x70, 0x0c, 0x48, 0xf7, 0x7f, 0x56, 0x58, 0x4c, 
	0x5c, 0xc6, 0x32, 0xca, 0x65, 0x64, 0x0d, 0xb9, 
	0x1b, 0x6b, 0xac, 0xce, 0x3a, 0x4d, 0xf6, 0xb4, 
	0x2c, 0xe7, 0xcc, 0x83, 0x88, 0x33, 0xd2, 0x87, 
	0xdb, 0x71, 0xe5, 0x09, 0xe3, 0xfd, 0x9b, 0x06, 
	0x0d, 0xdb, 0x20, 0xba, 0x5c, 0x51, 0xdc, 0xc5, 
	0x94, 0x8d, 0x46, 0xfb, 0xf6, 0x40, 0xdf, 0xe0, 
	0x44, 0x17, 0x82, 0xca, 0xb8, 0x5f, 0xa4, 0xac 
};


int main()
{
	uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	bool ok = true;

	for (int i = 0 ; i< sizeof(i_vectors)/sizeof(ecdhp256_tv_i); i++)
	{
		printf("ECDH Initiator Test %d \n", i );
		uint64_t success = Hacl_P256_ecp256dh_i(result, i_vectors[i].privateKey);
		ok = ok && (success == 0);
		ok = ok && compare_and_print(32, result, i_vectors[i].expectedPublicKeyX);
		ok = ok && compare_and_print(32, result + 32, i_vectors[i].expectedPublicKeyY);
	}

	
	uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	
	for (int i = 0 ; i< sizeof(i_vectors)/sizeof(ecdhp256_tv_i); i++)
	{

		printf("ECDH Responder Test %d\n", i );
		memcpy(pk, i_vectors[i].publicKeyX1,  32);
		memcpy(pk+32, i_vectors[i].publicKeyY1,  32);
	   
	    uint64_t success = Hacl_P256_ecp256dh_r(result, pk, i_vectors[i].privateKey);
	    ok = ok && (success == 0);
	    ok = ok && compare_and_print(32, result, i_vectors[i].expectedResult);
	}



	printf("Compression function test\n");

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


	printf("%s\n", "Wycheproof tests ECDH: ");
		
	for (int i = 0 ; i< sizeof(w_vectors)/sizeof(ecdhp256_w_i); i++)
	// for (int i = 174 ; i< 175; i++)
	{
		printf("ECDH Wycheproof Test %d ", i );

		uint8_t* decompressedPoint = (uint8_t*) malloc (sizeof (uint8_t) * 64);
		bool flagDecompress = Hacl_P256_decompression_not_compressed_form(w_vectors[i].publicKey, decompressedPoint);

		uint64_t success = Hacl_P256_ecp256dh_r(result, decompressedPoint, w_vectors[i].privateKey);

		uint64_t fDU = 0;
		if (flagDecompress = true)
			fDU = success;
		
		if (w_vectors[i].flag != 1) 
		{

			ok = ok && ((success & fDU) == w_vectors[i].flag);
			if (success == 0) {
				printf("%s\n", "");
				ok = ok && compare_and_print(32, result, w_vectors[i].sharedKey);
				}
		}
		else
			if (success == 0){
				printf("%s\n", "");
				ok = ok && compare_and_print(32, result, w_vectors[i].sharedKey);
			}


		if (!ok) 
			{
				printf("Test %d \n failed", i);
				break;
			}
		else
			printf("-- success \n");

	}


	printf("%s\n", "Wycheproof tests ECDSA: ");
		
	for (int i = 0 ; i< sizeof(w_ecdsa_vectors)/sizeof(ecdsap256_w_i) ; i++)
	{
		printf("ECDSA Wycheproof Test %d", i );
		
		uint32_t mLen = w_ecdsa_vectors[i].mLen;
		
		static uint8_t pk_ [64] = {0};
		for (int j = 0; j < 32; j++)
		{
			pk_[j] = w_ecdsa_vectors[i].publicX[j];
			pk_[j+32] = w_ecdsa_vectors[i].publicY[j];
		}


		bool resultVerification2 = Hacl_P256_ecdsa_verif_p256_sha2(mLen, w_ecdsa_vectors[i].message, pk_, w_ecdsa_vectors[i].r, w_ecdsa_vectors[i].s);	
		
		if ((w_ecdsa_vectors[i].flag == 18446744073709551615U) && (resultVerification2 == true))
		{
			ok = false;
		}	
		if ((w_ecdsa_vectors[i].flag == 0 && resultVerification2 == false))
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
		else
			printf(" -- success \n", i);


	}




  	if (ok) return EXIT_SUCCESS;
  	else return EXIT_FAILURE;
}



//Test 175
// prime = 2** 256 - 2**224 + 2**192 + 2**96 -1
// p = Zmod(prime)

// a = -3
// b = 41058363725152142129326129780047268409114441015993725554835256314039467401291

// bx = 0x31028f3377fc8f2b1967edaab90213acad0da9f50897f08f57537f78f1167447
// by = 0x43a1930189363bbde2ac4cbd1649cdc6f451add71dd2f16a8a867f2b17caa16b

// c = EllipticCurve(p, [a, b])
// p = c(bx, by) * (3 * 2**(31 * 8))
// print(hex(p.xy()[0]))


// test 339

// hash = 550593636553740323 * 2**0 + 15454474170993800 * 2 ** 64 + 17096616317808714211 * 2 ** 128 + 13500194041720771169 * 2 ** 192

// prime = 2** 256 - 2**224 + 2**192 + 2**96 -1
// p = Zmod(prime)

// r = 0x6f2347cab7dd76858fe0555ac3bc99048c4aacafdfb6bcbe05ea6c42c4934569
// s = 0xbb726660235793aa9957a61e76e00c2c435109cf9a15dd624d53f4301047856b
// order = 115792089210356248762697446949407573529996955224135760342422259061068512044369
// sinv = Integer(inverse_mod(s, order))
// u1 = (hash * sinv) % order
// u2 = (r * sinv) % order

// a = -3
// b = 41058363725152142129326129780047268409114441015993725554835256314039467401291

// bx = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
// by = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5

// c = EllipticCurve(p, [a, b])
// bp = c(bx, by)
// pk = c(0x5b812fd521aafa69835a849cce6fbdeb6983b442d2444fe70e134c027fc46963, 0x00838a40f2a36092e9004e92d8d940cf5638550ce672ce8b8d4e15eba5499249e9)
// x = Integer((bp * u1 + pk * u2).xy()[0]) % order
// print(x == r)