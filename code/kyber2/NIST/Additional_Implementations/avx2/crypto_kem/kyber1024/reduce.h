#ifndef REDUCE_H
#define REDUCE_H

#include <stdint.h>

int16_t reduce_avx(int16_t *r);
int16_t csubq_avx(int16_t *r);
int16_t frommont_avx(int16_t *r);

#endif
