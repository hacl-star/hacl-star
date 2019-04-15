#include <benchmark.h>

extern "C" {
#include <EverCrypt_AutoConfig2.h>
}

#include "bench_hash.h"

void print_config() {
  printf("CPU:");
  printf(" "); printf(EverCrypt_AutoConfig2_has_shaext() ? "+" : "-"); printf("SHAEXT");
  printf(" "); printf(EverCrypt_AutoConfig2_has_aesni() ? "+" : "-"); printf("AESNI");
  printf(" "); printf(EverCrypt_AutoConfig2_has_pclmulqdq() ? "+" : "-"); printf("PCLMULQDQ");
  printf(" "); printf(EverCrypt_AutoConfig2_has_avx() ? "+" : "-"); printf("AVX");
  printf(" "); printf(EverCrypt_AutoConfig2_has_avx2() ? "+" : "-"); printf("AVX2");
  printf(" "); printf(EverCrypt_AutoConfig2_has_bmi2() ? "+" : "-"); printf("BMI2");
  printf(" "); printf(EverCrypt_AutoConfig2_has_adx() ? "+" : "-"); printf("ADX");
  printf("\n");
}

void set_config(int shaext, int aesni, int pclmulqdq, int avx, int avx2, int bmi2, int adx) {
  EverCrypt_AutoConfig2_init();
  if (shaext == 0) EverCrypt_AutoConfig2_disable_shaext();
  if (aesni == 0) EverCrypt_AutoConfig2_disable_shaext();
  if (pclmulqdq == 0) EverCrypt_AutoConfig2_disable_shaext();
  if (avx == 0) EverCrypt_AutoConfig2_disable_shaext();
  if (avx2 == 0) EverCrypt_AutoConfig2_disable_shaext();
  if (bmi2 == 0) EverCrypt_AutoConfig2_disable_shaext();
  if (adx == 0) EverCrypt_AutoConfig2_disable_shaext();
}

int main(int argc, char const **argv)
{
  size_t samples = 20480;
  b_init();

  //EverCrypt_AutoConfig2_disable_vale();

  set_config(1, 1, 1, 1, 1, 1, 1);
  print_config();

  bench_hash(samples);

  return 0;
}