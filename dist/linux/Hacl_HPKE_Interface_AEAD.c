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


#include "Hacl_HPKE_Interface_AEAD.h"



void
(*Hacl_HPKE_Interface_AEAD_aead_encrypt(Spec_Agile_HPKE_ciphersuite cs))(
  u8 *x0,
  u8 *x1,
  u32 x2,
  u8 *x3,
  u32 x4,
  u8 *x5,
  u8 *x6
)
{
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__, "");
  KRML_HOST_EXIT(255U);
}

u32
(*Hacl_HPKE_Interface_AEAD_aead_decrypt(Spec_Agile_HPKE_ciphersuite cs))(
  u8 *x0,
  u8 *x1,
  u32 x2,
  u8 *x3,
  u32 x4,
  u8 *x5,
  u8 *x6
)
{
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__, "");
  KRML_HOST_EXIT(255U);
}

