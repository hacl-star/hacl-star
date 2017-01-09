#ifndef GFE_H
#define GFE_H

#include "crypto_int32.h"
#include "crypto_uint32.h"
#include "crypto_int64.h"
#include <sys/types.h>
typedef unsigned __int128 uint128_t;

typedef  uint128_t gfe;

void gfe_unpack(gfe *r, const unsigned char b[16]);

void gfe_pack(unsigned char r[16], const gfe *x);

void gfe_mul(gfe *r, const gfe x, const gfe y);
void gfe_square(gfe *r, const gfe x);
void gfe_mulconstz(gfe *r, const gfe x, const crypto_int32 c);
void gfe_mulconstd(gfe *r, const gfe x, const crypto_int32 c,const crypto_int64 *d);

void gfe_hadamard(gfe r[4]);

void gfe_invert(gfe *r, const gfe x);

#endif
