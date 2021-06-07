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



void master_branch_test()
{
	cycles a,b;
	clock_t t1,t2;
	uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 32);

	uint64_t len = SIZE;

	uint8_t scalar[SIZE];
	memset(scalar,'P',SIZE);
	
  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_i(result, scalar);

	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_i(result, scalar);
	
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
		Hacl_P256_ecp256dh_r(result, pk, privateKey);


	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecp256dh_r(result, pk, privateKey);
	
	b = cpucycles_end();
	
	t2 = clock();
	clock_t tdiff6 = t2 - t1;

	double timeLadderR = (((double)tdiff6) / CLOCKS_PER_SEC);
	double nsigsLadderR = ((double)ROUNDS) / timeLadderR;
	printf("HACL P-256 ECDH [Scalar Multiplication] PERF Ladder \n");
	printf("ECDH %8.2f mul/s\n",nsigsLadderR);

	cycles cdiff6 = b - a;
  	printf("cycles per function call:  %" PRIu64 " \n \n",(uint64_t)cdiff6/ROUNDS);

}




int main()
{

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
