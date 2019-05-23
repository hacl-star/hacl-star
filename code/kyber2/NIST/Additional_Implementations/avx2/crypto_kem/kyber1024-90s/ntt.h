#ifndef NTT_H
#define NTT_H

#include <stdint.h>

extern uint16_t zetas_exp[396];
extern uint16_t zetas_inv_exp[396];

void ntt_level0_avx(int16_t *r, const uint16_t *zetas);
void ntt_levels1t6_avx(int16_t *r, const uint16_t *zetas);
void invntt_levels0t5_avx(int16_t *r, const uint16_t *zetas);
void invntt_level6_avx(int16_t *r, const uint16_t *zetas);
void nttpack_avx(int16_t *r);
void nttunpack_avx(int16_t *r);
void basemul_avx(int16_t *r, const int16_t *a, const int16_t *b, uint16_t *zeta);
void basemul_acc_avx(int16_t *r, const int16_t *a, const int16_t *b, uint16_t *zeta);

void ntttobytes_avx(unsigned char *r, const int16_t *a);
void nttfrombytes_avx(int16_t *r, const unsigned char *a);

#endif
