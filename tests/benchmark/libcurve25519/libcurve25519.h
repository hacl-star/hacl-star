#ifndef _LIBCURVE25519_H_
#define _LIBCURVE25519_H_

#include <inttypes.h>
// #include <stdio.h>
// #include <stdlib.h>
// #include <string.h>
// #include <sys/types.h>
// #include <sys/stat.h>
// #include <fcntl.h>
// #include <unistd.h>
// #include <stdbool.h>
// #include <time.h>

typedef uint8_t u8;
typedef uint32_t u32;

static unsigned long stamp = 0;
int dummy;

enum { CURVE25519_POINT_SIZE = 32 };
u8 dummy_out[CURVE25519_POINT_SIZE];


#ifdef __cplusplus
extern "C" {
#endif

#define DECLARE(name) \
bool curve25519_ ## name(u8 mypublic[CURVE25519_POINT_SIZE], const u8 secret[CURVE25519_POINT_SIZE], const u8 basepoint[CURVE25519_POINT_SIZE]); \

DECLARE(donna64)
DECLARE(evercrypt64)
DECLARE(hacl51)
DECLARE(fiat64)
DECLARE(amd64)
DECLARE(precomp_bmi2)
DECLARE(precomp_adx)
DECLARE(openssl)

#ifdef __cplusplus
}
#endif

#endif