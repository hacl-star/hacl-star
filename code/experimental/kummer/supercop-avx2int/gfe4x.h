#ifndef GFE4X_H
#define GFE4X_H

#include "crypto_int32.h"
#include <immintrin.h>

typedef __m256i vec;

typedef struct {
  vec v[5];
} gfe4x;

void gfe4x_mul(gfe4x *,const gfe4x *,const gfe4x *);
void gfe4x_precompute(gfe4x *,const gfe4x *);
void gfe4x_mulprecomputed(gfe4x *,const gfe4x *,const gfe4x *,const gfe4x *);
void gfe4x_square(gfe4x *,const gfe4x *);
void gfe4x_mulconst(gfe4x *,const gfe4x *,const vec *);
void gfe4x_hadamard(gfe4x *,gfe4x *);
void gfe4x_select(gfe4x *,const gfe4x *,const gfe4x *,int);

#endif
