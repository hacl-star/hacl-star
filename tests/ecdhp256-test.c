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

#include "test_helpers.h"



int main()
{

	uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	bool ok = true;

	for (int i = 0 ; i< sizeof(i_vectors)/sizeof(ecdhp256_tv_i); i++)
	{
		printf("ECDH Initiator Test %d \n", i );
		uint64_t success = Hacl_Impl_P256_DH_ecp256dh_i(result, i_vectors[i].privateKey);
		ok = ok && (success == 0);
		ok = ok && compare_and_print(32, result, i_vectors[i].expectedPublicKeyX);
		ok = ok && compare_and_print(32, result + 32, i_vectors[i].expectedPublicKeyY);
	}

	
	uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	
	for (int i = 0 ; i< sizeof(i_vectors)/sizeof(ecdhp256_tv_i); i++)
	{

		printf("ECDH Responder Test %d\n", i );
		memcpy(pk, i_vectors[0].publicKeyX1,  32);
		memcpy(pk+32, i_vectors[0].publicKeyY1,  32);
	   
	    uint64_t success = Hacl_Impl_P256_DH_ecp256dh_r(result, pk, i_vectors[0].privateKey);
	    ok = ok && (success == 0);
	    ok = ok && compare_and_print(32, result, i_vectors[0].expectedResult);
	}


  	if (ok) return EXIT_SUCCESS;
  	else return EXIT_FAILURE;


}