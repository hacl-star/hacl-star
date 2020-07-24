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
		printf("ECDH Wycheproof Test %d \n", i );
		compare_and_print(65, w_vectors[i].publicKey, w_vectors[i].publicKey);

		uint8_t* decompressedPoint = (uint8_t*) malloc (sizeof (uint8_t) * 64);
		bool flagDecompress = Hacl_P256_decompression_not_compressed_form(w_vectors[i].publicKey, decompressedPoint);

		uint64_t success = Hacl_P256_ecp256dh_r(result, decompressedPoint, w_vectors[i].privateKey);

		uint64_t fDU = 0;
		if (flagDecompress = true)
			fDU = success;
		
		compare_and_print(64, result, result);


		if (w_vectors[i].flag != 1) 
		{

			ok = ok && ((success & fDU) == w_vectors[i].flag);
			if (success == 0)
				ok = ok && compare_and_print(32, result, w_vectors[i].sharedKey);
		}
		else
			if (success == 0)
				ok = ok && compare_and_print(32, result, w_vectors[i].sharedKey);


		if (!ok) 
			{
				printf("Test %d \n failed", i);
				break;
			}

	}


	// printf("%s\n", "Wycheproof tests ECDSA: ");
	static uint8_t m0 [6] = {0x31, 0x32, 0x33, 0x34, 0x30, 0x30};

	static uint8_t pk0 [64] = {
		0x0a, 0xd9, 0x95, 0x00, 0x28, 0x8d, 0x46, 0x69, 0x40, 0x03, 0x1d, 0x72, 0xa9, 0xf5, 0x44, 0x5a, 0x4d, 0x43, 0x78, 0x46, 0x40, 0x85, 0x5b, 0xf0, 0xa6, 0x98, 0x74, 0xd2, 0xde, 0x5f, 0xe1, 0x03,
		0xc5, 0x01, 0x1e, 0x6e, 0xf2, 0xc4, 0x2d, 0xcd, 0x50, 0xd5, 0xd3, 0xd2, 0x9f, 0x99, 0xae, 0x6e, 0xba, 0x2c, 0x80, 0xc9, 0x24, 0x4f, 0x4c, 0x54, 0x22, 0xf0, 0x97, 0x9f, 0xf0, 0xc3, 0xba, 0x5e
	};
	
	static uint8_t r[32] = {
		0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
		0x43, 0x19, 0x05, 0x53, 0x58, 0xe8, 0x61, 0x7b, 
		0x0c, 0x46, 0x35, 0x3d, 0x03, 0x9c, 0xda, 0xab
	};


	static uint8_t s[32] = {
		0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 
		0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
		0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 
		0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63, 0x25, 0x4e
	};


	bool resultVerification = Hacl_P256_ecdsa_verif_p256_sha2(6, m0, pk0, r, s);

	if (!resultVerification) 
		{
			printf("Test ECDSA %d  failed \n", 0);
		}
	else
		printf("Test ECDSA %d succeeded \n", 0);

	ok = ok && resultVerification;



	printf("%s\n", "Wycheproof 2");


	static uint8_t pk1 [64] = {
		0x5b, 0x81, 0x2f, 0xd5, 0x21, 0xaa, 0xfa, 0x69, 
		0x83, 0x5a, 0x84, 0x9c, 0xce, 0x6f, 0xbd, 0xeb, 
		0x69, 0x83, 0xb4, 0x42, 0xd2, 0x44, 0x4f, 0xe7, 
		0x0e, 0x13, 0x4c, 0x02, 0x7f, 0xc4, 0x69, 0x63,

		0x83, 0x8a, 0x40, 0xf2, 0xa3, 0x60, 0x92, 0xe9, 
		0x00, 0x4e, 0x92, 0xd8, 0xd9, 0x40, 0xcf, 0x56, 
		0x38, 0x55, 0x0c, 0xe6, 0x72, 0xce, 0x8b, 0x8d, 
		0x4e, 0x15, 0xeb, 0xa5, 0x49, 0x92, 0x49, 0xe9
	};


	static uint8_t r1[32]= {
		0x6f, 0x23, 0x47, 0xca, 0xb7, 0xdd, 0x76, 0x85, 
		0x8f, 0xe0, 0x55, 0x5a, 0xc3, 0xbc, 0x99, 0x04, 
		0x8c, 0x4a, 0xac, 0xaf, 0xdf, 0xb6, 0xbc, 0xbe, 
		0x05, 0xea, 0x6c, 0x42, 0xc4, 0x93, 0x45, 0x69
	};

	static uint8_t s1[32] = {
		0xbb, 0x72, 0x66, 0x60, 0x23, 0x57, 0x93, 0xaa, 
		0x99, 0x57, 0xa6, 0x1e, 0x76, 0xe0, 0x0c, 0x2c, 
		0x43, 0x51, 0x09, 0xcf, 0x9a, 0x15, 0xdd, 0x62, 
		0x4d, 0x53, 0xf4, 0x30, 0x10, 0x47, 0x85, 0x6b
	};



	bool resultVerification1 = Hacl_P256_ecdsa_verif_p256_sha2(6, m0, pk1, r1, s1);

	if (!resultVerification1) 
		{
			printf("Test ECDSA %d  failed \n", 1);
		}
	else
		printf("Test ECDSA %d succeeded \n", 1);

	ok = ok && resultVerification1;




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