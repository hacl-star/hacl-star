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

/* SNIPPET_START: cpu_has_shaext */

static bool cpu_has_shaext[1U] = { false };

/* SNIPPET_END: cpu_has_shaext */

/* SNIPPET_START: cpu_has_aesni */

static bool cpu_has_aesni[1U] = { false };

/* SNIPPET_END: cpu_has_aesni */

/* SNIPPET_START: cpu_has_pclmulqdq */

static bool cpu_has_pclmulqdq[1U] = { false };

/* SNIPPET_END: cpu_has_pclmulqdq */

/* SNIPPET_START: cpu_has_avx2 */

static bool cpu_has_avx2[1U] = { false };

/* SNIPPET_END: cpu_has_avx2 */

/* SNIPPET_START: cpu_has_avx */

static bool cpu_has_avx[1U] = { false };

/* SNIPPET_END: cpu_has_avx */

/* SNIPPET_START: cpu_has_bmi2 */

static bool cpu_has_bmi2[1U] = { false };

/* SNIPPET_END: cpu_has_bmi2 */

/* SNIPPET_START: cpu_has_adx */

static bool cpu_has_adx[1U] = { false };

/* SNIPPET_END: cpu_has_adx */

/* SNIPPET_START: cpu_has_sse */

static bool cpu_has_sse[1U] = { false };

/* SNIPPET_END: cpu_has_sse */

/* SNIPPET_START: cpu_has_movbe */

static bool cpu_has_movbe[1U] = { false };

/* SNIPPET_END: cpu_has_movbe */

/* SNIPPET_START: cpu_has_rdrand */

static bool cpu_has_rdrand[1U] = { false };

/* SNIPPET_END: cpu_has_rdrand */

/* SNIPPET_START: cpu_has_avx512 */

static bool cpu_has_avx512[1U] = { false };

/* SNIPPET_END: cpu_has_avx512 */

/* SNIPPET_START: user_wants_hacl */

static bool user_wants_hacl[1U] = { true };

/* SNIPPET_END: user_wants_hacl */

/* SNIPPET_START: user_wants_vale */

static bool user_wants_vale[1U] = { true };

/* SNIPPET_END: user_wants_vale */

/* SNIPPET_START: user_wants_openssl */

static bool user_wants_openssl[1U] = { true };

/* SNIPPET_END: user_wants_openssl */

/* SNIPPET_START: user_wants_bcrypt */

static bool user_wants_bcrypt[1U] = { false };

/* SNIPPET_END: user_wants_bcrypt */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_shaext */

bool EverCrypt_AutoConfig2_has_shaext()
{
  return cpu_has_shaext[0U];
}

/* SNIPPET_END: EverCrypt_AutoConfig2_has_shaext */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_aesni */

bool EverCrypt_AutoConfig2_has_aesni()
{
  return cpu_has_aesni[0U];
}

/* SNIPPET_END: EverCrypt_AutoConfig2_has_aesni */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_pclmulqdq */

bool EverCrypt_AutoConfig2_has_pclmulqdq()
{
  return cpu_has_pclmulqdq[0U];
}

/* SNIPPET_END: EverCrypt_AutoConfig2_has_pclmulqdq */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_avx2 */

bool EverCrypt_AutoConfig2_has_avx2()
{
  return cpu_has_avx2[0U];
}

/* SNIPPET_END: EverCrypt_AutoConfig2_has_avx2 */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_avx */

bool EverCrypt_AutoConfig2_has_avx()
{
  return cpu_has_avx[0U];
}

/* SNIPPET_END: EverCrypt_AutoConfig2_has_avx */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_bmi2 */

bool EverCrypt_AutoConfig2_has_bmi2()
{
  return cpu_has_bmi2[0U];
}

/* SNIPPET_END: EverCrypt_AutoConfig2_has_bmi2 */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_adx */

bool EverCrypt_AutoConfig2_has_adx()
{
  return cpu_has_adx[0U];
}

/* SNIPPET_END: EverCrypt_AutoConfig2_has_adx */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_sse */

bool EverCrypt_AutoConfig2_has_sse()
{
  return cpu_has_sse[0U];
}

/* SNIPPET_END: EverCrypt_AutoConfig2_has_sse */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_movbe */

bool EverCrypt_AutoConfig2_has_movbe()
{
  return cpu_has_movbe[0U];
}

/* SNIPPET_END: EverCrypt_AutoConfig2_has_movbe */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_rdrand */

bool EverCrypt_AutoConfig2_has_rdrand()
{
  return cpu_has_rdrand[0U];
}

/* SNIPPET_END: EverCrypt_AutoConfig2_has_rdrand */

/* SNIPPET_START: EverCrypt_AutoConfig2_has_avx512 */

bool EverCrypt_AutoConfig2_has_avx512()
{
  return cpu_has_avx512[0U];
}

/* SNIPPET_END: EverCrypt_AutoConfig2_has_avx512 */

/* SNIPPET_START: EverCrypt_AutoConfig2_wants_vale */

bool EverCrypt_AutoConfig2_wants_vale()
{
  return user_wants_vale[0U];
}

/* SNIPPET_END: EverCrypt_AutoConfig2_wants_vale */

/* SNIPPET_START: EverCrypt_AutoConfig2_wants_hacl */

bool EverCrypt_AutoConfig2_wants_hacl()
{
  return user_wants_hacl[0U];
}

/* SNIPPET_END: EverCrypt_AutoConfig2_wants_hacl */

/* SNIPPET_START: EverCrypt_AutoConfig2_wants_openssl */

bool EverCrypt_AutoConfig2_wants_openssl()
{
  return user_wants_openssl[0U];
}

/* SNIPPET_END: EverCrypt_AutoConfig2_wants_openssl */

/* SNIPPET_START: EverCrypt_AutoConfig2_wants_bcrypt */

bool EverCrypt_AutoConfig2_wants_bcrypt()
{
  return user_wants_bcrypt[0U];
}

/* SNIPPET_END: EverCrypt_AutoConfig2_wants_bcrypt */

/* SNIPPET_START: EverCrypt_AutoConfig2_recall */

void EverCrypt_AutoConfig2_recall()
{
  
}

/* SNIPPET_END: EverCrypt_AutoConfig2_recall */

/* SNIPPET_START: EverCrypt_AutoConfig2_init */

void EverCrypt_AutoConfig2_init()
{
  #if EVERCRYPT_TARGETCONFIG_X64
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

/* SNIPPET_END: EverCrypt_AutoConfig2_init */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_avx2 */

void EverCrypt_AutoConfig2_disable_avx2()
{
  cpu_has_avx2[0U] = false;
}

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_avx2 */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_avx */

void EverCrypt_AutoConfig2_disable_avx()
{
  cpu_has_avx[0U] = false;
}

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_avx */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_bmi2 */

void EverCrypt_AutoConfig2_disable_bmi2()
{
  cpu_has_bmi2[0U] = false;
}

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_bmi2 */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_adx */

void EverCrypt_AutoConfig2_disable_adx()
{
  cpu_has_adx[0U] = false;
}

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_adx */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_shaext */

void EverCrypt_AutoConfig2_disable_shaext()
{
  cpu_has_shaext[0U] = false;
}

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_shaext */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_aesni */

void EverCrypt_AutoConfig2_disable_aesni()
{
  cpu_has_aesni[0U] = false;
}

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_aesni */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_pclmulqdq */

void EverCrypt_AutoConfig2_disable_pclmulqdq()
{
  cpu_has_pclmulqdq[0U] = false;
}

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_pclmulqdq */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_sse */

void EverCrypt_AutoConfig2_disable_sse()
{
  cpu_has_sse[0U] = false;
}

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_sse */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_movbe */

void EverCrypt_AutoConfig2_disable_movbe()
{
  cpu_has_movbe[0U] = false;
}

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_movbe */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_rdrand */

void EverCrypt_AutoConfig2_disable_rdrand()
{
  cpu_has_rdrand[0U] = false;
}

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_rdrand */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_avx512 */

void EverCrypt_AutoConfig2_disable_avx512()
{
  cpu_has_avx512[0U] = false;
}

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_avx512 */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_vale */

void EverCrypt_AutoConfig2_disable_vale()
{
  user_wants_vale[0U] = false;
}

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_vale */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_hacl */

void EverCrypt_AutoConfig2_disable_hacl()
{
  user_wants_hacl[0U] = false;
}

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_hacl */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_openssl */

void EverCrypt_AutoConfig2_disable_openssl()
{
  user_wants_openssl[0U] = false;
}

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_openssl */

/* SNIPPET_START: EverCrypt_AutoConfig2_disable_bcrypt */

void EverCrypt_AutoConfig2_disable_bcrypt()
{
  user_wants_bcrypt[0U] = false;
}

/* SNIPPET_END: EverCrypt_AutoConfig2_disable_bcrypt */

