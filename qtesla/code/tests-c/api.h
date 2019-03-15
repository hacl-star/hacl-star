/*************************************************************************************
* qTESLA: an efficient post-quantum signature scheme based on the R-LWE problem
*
* Abstract: API header file
**************************************************************************************/

#include "params.h"
#include <stdint.h>


#if defined(_qTESLA_I_)
  #define CRYPTO_ALGNAME "qTesla-I"
#elif defined(_qTESLA_III_speed_)
  #define CRYPTO_ALGNAME "qTesla-III-speed"
#elif defined(_qTESLA_III_size_)
  #define CRYPTO_ALGNAME "qTesla-III-size"
#elif defined(_qTESLA_p_I_)
  #define CRYPTO_ALGNAME "qTesla-p-I"
#elif defined(_qTESLA_p_III_)
  #define CRYPTO_ALGNAME "qTesla-p-III"
#endif

#define CRYPTO_RANDOMBYTES 32
#define CRYPTO_SEEDBYTES 32
#define CRYPTO_C_BYTES 32
#define HM_BYTES 64

// Contains signature (z,c). z is a polynomial bounded by B, c is the output of a hashed string
#define CRYPTO_BYTES ((PARAM_N*PARAM_D+7)/8 + CRYPTO_C_BYTES)
#if defined(_qTESLA_I_) || defined(_qTESLA_III_speed_) || defined(_qTESLA_III_size_)
  // Contains polynomial s and e, and seeds seed_a and seed_y
  #define CRYPTO_SECRETKEYBYTES (2*PARAM_S_BITS*PARAM_N/8 + 2*CRYPTO_SEEDBYTES)
  // Contains seed_a and polynomial t
  #define CRYPTO_PUBLICKEYBYTES ((PARAM_N*PARAM_Q_LOG+7)/8 + CRYPTO_SEEDBYTES)
#elif defined(_qTESLA_p_I_) || defined(_qTESLA_p_III_)
  // Contains polynomial s and e, and seeds seed_a and seed_y
  #define CRYPTO_SECRETKEYBYTES (sizeof(int8_t)*PARAM_N + sizeof(int8_t)*PARAM_N*PARAM_K + 2*CRYPTO_SEEDBYTES)
  // Contains seed_a and polynomials t
  #define CRYPTO_PUBLICKEYBYTES ((PARAM_Q_LOG*PARAM_N*PARAM_K+7)/8 + CRYPTO_SEEDBYTES)
#else
  #error Unrecognized parameter set
#endif

