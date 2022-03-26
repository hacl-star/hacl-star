/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "EverCrypt_AutoConfig2.h"

#include "internal/Vale.h"

static bool cpu_has_shaext[1U] = { false };

static bool cpu_has_aesni[1U] = { false };

static bool cpu_has_pclmulqdq[1U] = { false };

static bool cpu_has_avx2[1U] = { false };

static bool cpu_has_avx[1U] = { false };

static bool cpu_has_bmi2[1U] = { false };

static bool cpu_has_adx[1U] = { false };

static bool cpu_has_sse[1U] = { false };

static bool cpu_has_movbe[1U] = { false };

static bool cpu_has_rdrand[1U] = { false };

static bool cpu_has_avx512[1U] = { false };

static bool user_wants_hacl[1U] = { true };

static bool user_wants_vale[1U] = { true };

static bool user_wants_openssl[1U] = { true };

static bool user_wants_bcrypt[1U] = { false };

bool EverCrypt_AutoConfig2_has_shaext()
{
  return cpu_has_shaext[0U];
}

bool EverCrypt_AutoConfig2_has_aesni()
{
  return cpu_has_aesni[0U];
}

bool EverCrypt_AutoConfig2_has_pclmulqdq()
{
  return cpu_has_pclmulqdq[0U];
}

bool EverCrypt_AutoConfig2_has_avx2()
{
  return cpu_has_avx2[0U];
}

bool EverCrypt_AutoConfig2_has_avx()
{
  return cpu_has_avx[0U];
}

bool EverCrypt_AutoConfig2_has_bmi2()
{
  return cpu_has_bmi2[0U];
}

bool EverCrypt_AutoConfig2_has_adx()
{
  return cpu_has_adx[0U];
}

bool EverCrypt_AutoConfig2_has_sse()
{
  return cpu_has_sse[0U];
}

bool EverCrypt_AutoConfig2_has_movbe()
{
  return cpu_has_movbe[0U];
}

bool EverCrypt_AutoConfig2_has_rdrand()
{
  return cpu_has_rdrand[0U];
}

bool EverCrypt_AutoConfig2_has_avx512()
{
  return cpu_has_avx512[0U];
}

KRML_DEPRECATED("")

bool EverCrypt_AutoConfig2_wants_vale()
{
  return user_wants_vale[0U];
}

bool EverCrypt_AutoConfig2_wants_hacl()
{
  return user_wants_hacl[0U];
}

bool EverCrypt_AutoConfig2_wants_openssl()
{
  return user_wants_openssl[0U];
}

bool EverCrypt_AutoConfig2_wants_bcrypt()
{
  return user_wants_bcrypt[0U];
}

void EverCrypt_AutoConfig2_recall()
{

}

void EverCrypt_AutoConfig2_init()
{
  #if HACL_CAN_COMPILE_VALE
  uint64_t scrut = check_aesni();
  if (scrut != (uint64_t)0U)
  {
    cpu_has_aesni[0U] = true;
    cpu_has_pclmulqdq[0U] = true;
  }
  uint64_t scrut0 = check_sha();
  if (scrut0 != (uint64_t)0U)
  {
    cpu_has_shaext[0U] = true;
  }
  uint64_t scrut1 = check_adx_bmi2();
  if (scrut1 != (uint64_t)0U)
  {
    cpu_has_bmi2[0U] = true;
    cpu_has_adx[0U] = true;
  }
  uint64_t scrut2 = check_avx();
  if (scrut2 != (uint64_t)0U)
  {
    uint64_t scrut3 = check_osxsave();
    if (scrut3 != (uint64_t)0U)
    {
      uint64_t scrut4 = check_avx_xcr0();
      if (scrut4 != (uint64_t)0U)
      {
        cpu_has_avx[0U] = true;
      }
    }
  }
  uint64_t scrut3 = check_avx2();
  if (scrut3 != (uint64_t)0U)
  {
    uint64_t scrut4 = check_osxsave();
    if (scrut4 != (uint64_t)0U)
    {
      uint64_t scrut5 = check_avx_xcr0();
      if (scrut5 != (uint64_t)0U)
      {
        cpu_has_avx2[0U] = true;
      }
    }
  }
  uint64_t scrut4 = check_sse();
  if (scrut4 != (uint64_t)0U)
  {
    cpu_has_sse[0U] = true;
  }
  uint64_t scrut5 = check_movbe();
  if (scrut5 != (uint64_t)0U)
  {
    cpu_has_movbe[0U] = true;
  }
  uint64_t scrut6 = check_rdrand();
  if (scrut6 != (uint64_t)0U)
  {
    cpu_has_rdrand[0U] = true;
  }
  uint64_t scrut7 = check_avx512();
  if (scrut7 != (uint64_t)0U)
  {
    uint64_t scrut8 = check_osxsave();
    if (scrut8 != (uint64_t)0U)
    {
      uint64_t scrut9 = check_avx_xcr0();
      if (scrut9 != (uint64_t)0U)
      {
        uint64_t scrut10 = check_avx512_xcr0();
        if (scrut10 != (uint64_t)0U)
        {
          cpu_has_avx512[0U] = true;
        }
      }
    }
  }
  #endif
  user_wants_hacl[0U] = true;
  user_wants_vale[0U] = true;
  user_wants_bcrypt[0U] = false;
  user_wants_openssl[0U] = true;
}

void EverCrypt_AutoConfig2_disable_avx2()
{
  cpu_has_avx2[0U] = false;
}

void EverCrypt_AutoConfig2_disable_avx()
{
  cpu_has_avx[0U] = false;
}

void EverCrypt_AutoConfig2_disable_bmi2()
{
  cpu_has_bmi2[0U] = false;
}

void EverCrypt_AutoConfig2_disable_adx()
{
  cpu_has_adx[0U] = false;
}

void EverCrypt_AutoConfig2_disable_shaext()
{
  cpu_has_shaext[0U] = false;
}

void EverCrypt_AutoConfig2_disable_aesni()
{
  cpu_has_aesni[0U] = false;
}

void EverCrypt_AutoConfig2_disable_pclmulqdq()
{
  cpu_has_pclmulqdq[0U] = false;
}

void EverCrypt_AutoConfig2_disable_sse()
{
  cpu_has_sse[0U] = false;
}

void EverCrypt_AutoConfig2_disable_movbe()
{
  cpu_has_movbe[0U] = false;
}

void EverCrypt_AutoConfig2_disable_rdrand()
{
  cpu_has_rdrand[0U] = false;
}

void EverCrypt_AutoConfig2_disable_avx512()
{
  cpu_has_avx512[0U] = false;
}

void EverCrypt_AutoConfig2_disable_vale()
{
  user_wants_vale[0U] = false;
}

void EverCrypt_AutoConfig2_disable_hacl()
{
  user_wants_hacl[0U] = false;
}

void EverCrypt_AutoConfig2_disable_openssl()
{
  user_wants_openssl[0U] = false;
}

void EverCrypt_AutoConfig2_disable_bcrypt()
{
  user_wants_bcrypt[0U] = false;
}

bool EverCrypt_AutoConfig2_has_vec128()
{
  bool avx = EverCrypt_AutoConfig2_has_avx();
  bool other = has_vec128_not_avx();
  return avx || other;
}

bool EverCrypt_AutoConfig2_has_vec256()
{
  bool avx2 = EverCrypt_AutoConfig2_has_avx2();
  bool other = has_vec256_not_avx2();
  return avx2 || other;
}

