extern "C" {
#include <EverCrypt_AutoConfig2.h>
}

#include "benchmark.h"

void b_init()
{
  srand(0);
}

extern void b_randomize(char *buf, size_t buf_sz)
{
  for (int i = 0; i < buf_sz; i++)
    buf[i] = rand() % 8;
}

void Benchmark::print_config(std::ostream & rs)
{
  rs << "// Config: ";
  rs << " " << (EverCrypt_AutoConfig2_has_shaext() ? "+" : "-") << "SHAEXT";
  rs << " " << (EverCrypt_AutoConfig2_has_aesni() ? "+" : "-") << "AESNI";
  rs << " " << (EverCrypt_AutoConfig2_has_pclmulqdq() ? "+" : "-") << "PCLMULQDQ";
  rs << " " << (EverCrypt_AutoConfig2_has_avx() ? "+" : "-") << "AVX";
  rs << " " << (EverCrypt_AutoConfig2_has_avx2() ? "+" : "-") << "AVX2";
  rs << " " << (EverCrypt_AutoConfig2_has_bmi2() ? "+" : "-") << "BMI2";
  rs << " " << (EverCrypt_AutoConfig2_has_adx() ? "+" : "-") << "ADX";
  rs << " " << (EverCrypt_AutoConfig2_wants_hacl() ? "+" : "-") << "HACL";
  rs << " " << (EverCrypt_AutoConfig2_wants_vale() ? "+" : "-") << "VALE";
  rs << "\n";
}

void Benchmark::set_config(int shaext, int aesni, int pclmulqdq, int avx, int avx2, int bmi2, int adx, int hacl, int vale)
{
  EverCrypt_AutoConfig2_init();
  if (shaext == 0) EverCrypt_AutoConfig2_disable_shaext();
  if (aesni == 0) EverCrypt_AutoConfig2_disable_aesni();
  if (pclmulqdq == 0) EverCrypt_AutoConfig2_disable_pclmulqdq();
  if (avx == 0) EverCrypt_AutoConfig2_disable_avx();
  if (avx2 == 0) EverCrypt_AutoConfig2_disable_avx2();

  // No way to disable these?
  // if (bmi2 == 0) EverCrypt_AutoConfig2_disable_bmi2();
  // if (adx == 0) EverCrypt_AutoConfig2_disable_adx();

  if (hacl == 0) EverCrypt_AutoConfig2_disable_hacl();
  if (vale == 0) EverCrypt_AutoConfig2_disable_vale();
}