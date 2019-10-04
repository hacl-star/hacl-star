#ifndef _FIAT_CURVE25519_
#define _FIAT_CURVE25519_

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>

typedef uint8_t u8;

int crypto_scalarmult(u8 *mypublic, const u8 *secret, const u8 *basepoint);

#ifdef __cplusplus
}
#endif

#endif
