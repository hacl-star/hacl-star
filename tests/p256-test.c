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

#include <openssl/evp.h>
#include <openssl/ecdsa.h>


// uint8_t
// siggen_vectors_low0[128U] =
//   {
//     (uint8_t)89U, (uint8_t)5U, (uint8_t)35U, (uint8_t)136U, (uint8_t)119U, (uint8_t)199U,
//     (uint8_t)116U, (uint8_t)33U, (uint8_t)247U, (uint8_t)62U, (uint8_t)67U, (uint8_t)238U,
//     (uint8_t)61U, (uint8_t)166U, (uint8_t)242U, (uint8_t)217U, (uint8_t)226U, (uint8_t)204U,
//     (uint8_t)173U, (uint8_t)95U, (uint8_t)201U, (uint8_t)66U, (uint8_t)220U, (uint8_t)236U,
//     (uint8_t)12U, (uint8_t)189U, (uint8_t)37U, (uint8_t)72U, (uint8_t)41U, (uint8_t)53U,
//     (uint8_t)250U, (uint8_t)175U, (uint8_t)65U, (uint8_t)105U, (uint8_t)131U, (uint8_t)254U,
//     (uint8_t)22U, (uint8_t)91U, (uint8_t)26U, (uint8_t)4U, (uint8_t)94U, (uint8_t)226U,
//     (uint8_t)188U, (uint8_t)210U, (uint8_t)230U, (uint8_t)220U, (uint8_t)163U, (uint8_t)189U,
//     (uint8_t)244U, (uint8_t)108U, (uint8_t)67U, (uint8_t)16U, (uint8_t)167U, (uint8_t)70U,
//     (uint8_t)31U, (uint8_t)154U, (uint8_t)55U, (uint8_t)150U, (uint8_t)12U, (uint8_t)166U,
//     (uint8_t)114U, (uint8_t)211U, (uint8_t)254U, (uint8_t)181U, (uint8_t)71U, (uint8_t)62U,
//     (uint8_t)37U, (uint8_t)54U, (uint8_t)5U, (uint8_t)251U, (uint8_t)29U, (uint8_t)223U,
//     (uint8_t)210U, (uint8_t)128U, (uint8_t)101U, (uint8_t)181U, (uint8_t)60U, (uint8_t)181U,
//     (uint8_t)133U, (uint8_t)138U, (uint8_t)138U, (uint8_t)210U, (uint8_t)129U, (uint8_t)117U,
//     (uint8_t)191U, (uint8_t)155U, (uint8_t)211U, (uint8_t)134U, (uint8_t)165U, (uint8_t)228U,
//     (uint8_t)113U, (uint8_t)234U, (uint8_t)122U, (uint8_t)101U, (uint8_t)193U, (uint8_t)124U,
//     (uint8_t)201U, (uint8_t)52U, (uint8_t)169U, (uint8_t)215U, (uint8_t)145U, (uint8_t)233U,
//     (uint8_t)20U, (uint8_t)145U, (uint8_t)235U, (uint8_t)55U, (uint8_t)84U, (uint8_t)208U,
//     (uint8_t)55U, (uint8_t)153U, (uint8_t)121U, (uint8_t)15U, (uint8_t)226U, (uint8_t)211U,
//     (uint8_t)8U, (uint8_t)209U, (uint8_t)97U, (uint8_t)70U, (uint8_t)213U, (uint8_t)201U,
//     (uint8_t)176U, (uint8_t)208U, (uint8_t)222U, (uint8_t)189U, (uint8_t)151U, (uint8_t)215U,
//     (uint8_t)156U, (uint8_t)232U
//   };

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
siggen_vectors_low3[32U] =
  {
    (uint8_t)206U, (uint8_t)64U, (uint8_t)20U, (uint8_t)198U, (uint8_t)136U, (uint8_t)17U,
    (uint8_t)249U, (uint8_t)162U, (uint8_t)26U, (uint8_t)31U, (uint8_t)219U, (uint8_t)44U,
    (uint8_t)14U, (uint8_t)97U, (uint8_t)19U, (uint8_t)224U, (uint8_t)109U, (uint8_t)183U,
    (uint8_t)202U, (uint8_t)147U, (uint8_t)183U, (uint8_t)64U, (uint8_t)78U, (uint8_t)120U,
    (uint8_t)220U, (uint8_t)124U, (uint8_t)205U, (uint8_t)92U, (uint8_t)168U, (uint8_t)154U,
    (uint8_t)76U, (uint8_t)169U
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


bool print_result(int in_len, uint8_t* comp, uint8_t* exp) {
  return compare_and_print(in_len, comp, exp);
}

void printTemp(uint8_t* b){
  for (int i = 0; i< 32; i++)
  {
    printf("%x", b[i]);
  }

  printf("\n");
}

#define ROUNDS 16384
#define SIZE   16384

bool testImplementationHacl()
{
	uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint64_t flag = Hacl_Interface_P256_ecdsa_sign_p256_without_hash(result, digest, prKey, nonce);
	bool s0 = compare_and_print(32, result, siggen_vectors_low5);
	bool s1 = compare_and_print(32, result + 32, siggen_vectors_low6);
	return s0 && s1 && (flag == 0);
}

bool testImplementationOpenssl()
{
	EC_KEY *eckey = EC_KEY_new();
	if (eckey == NULL) {
      return false;
    }

	uint32_t buf_len = ECDSA_size(eckey); 
    uint8_t length = 64;
    uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * length);
    EC_KEY_set_private_key(eckey, prKey);

    EC_GROUP *group = EC_GROUP_new_by_curve_name(NID_X9_62_prime256v1);
    EC_KEY_set_group(eckey, group);


    bool flag = ECDSA_sign(0, digest, 32, result, &buf_len, eckey);
    printf("%d\n", flag);
    return (flag == 0);
}


int main()
{
	if (!testImplementationHacl())
	{
		printf("%s\n", "Test Implementation failed for Hacl* ECDSA");
		return -1;
	}

	if (!testImplementationOpenssl())
	{
		return -1;
	}



	cycles a,b;
	clock_t t1,t2;
	uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 64);

	uint64_t len = SIZE;
	uint8_t plain[SIZE];
	memset(plain,'P',SIZE);
	
	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
  	{
		  Hacl_Interface_P256_ecdsa_sign_p256_without_hash(plain, plain, prKey, nonce);
  	}
	
	b = cpucycles_end();
	t2 = clock();
	clock_t tdiff1 = t2 - t1;
	cycles cdiff1 = b - a;



  	EC_KEY *eckey = EC_KEY_new();
	if (eckey == NULL) {
      return false;
    }

	
  // memset(plain,'P',SIZE);
  EC_KEY_set_private_key(eckey, prKey);

    EC_GROUP *group = EC_GROUP_new_by_curve_name(NID_X9_62_prime256v1);
    EC_KEY_set_group(eckey, group);
    unsigned int sig_len = ECDSA_size(eckey);
    unsigned char *signature = OPENSSL_malloc(sig_len);
    EC_KEY_generate_key(eckey);


  t1 = clock();
    a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
  	{
		  ECDSA_sign(0, signature + 40, 32, signature, &sig_len, eckey);

  	}
	
	b = cpucycles_end();
	t2 = clock();
	clock_t tdiff2 = t2 - t1;
	cycles cdiff2 = b - a;

	uint64_t count = ROUNDS * SIZE;
	printf("Hacl ECDSA (without hasing) PERF: %d\n"); 
	print_time(count,tdiff1,cdiff1);

	printf("OpenSSL ECDSA (without hasing) PERF: %d\n"); 
	print_time(count,tdiff2,cdiff2);

}

// Doing 256 bits sign ecdsa's for 10s: 458415 256 bits ECDSA signs in 10.00s 
// Doing 256 bits verify ecdsa's for 10s: 164425 256 bits ECDSA verify in 10.00s
