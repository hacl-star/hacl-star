#ifndef GFE_H
#define GFE_H

#include "crypto_int32.h"
#include "crypto_uint32.h"
#include "crypto_int64.h"

typedef struct{
  crypto_uint32 v[5];
} gfe;

void gfe_unpack(gfe *r, const unsigned char b[16]);

void gfe_pack(unsigned char r[16], const gfe *x);

void gfe_mul(gfe *r, const gfe *x, const gfe *y);
void gfe_square(gfe *r, const gfe *x);
void gfe_mulconst(gfe *r, const gfe *x, crypto_int32 c,const crypto_int64 *d);

void gfe_hadamard(gfe r[4]);

void gfe_invert(gfe *r, const gfe *x);

#endif
