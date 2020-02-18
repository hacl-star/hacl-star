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

#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>

#ifndef __Hacl_Impl_Creation_GenKey_H
#define __Hacl_Impl_Creation_GenKey_H

#include "Hacl_Impl_PKCS11_Creation_GenKey.h"


typedef struct FStar_Pervasives_either__uint64_t_Hacl_Impl_PKCS11_Result_exception_t_s
{
  FStar_Pervasives_either__Prims_int_Hacl_Impl_PKCS11_Result_exception_t_tags tag;
  union {
    uint64_t case_Inl;
    Hacl_Impl_PKCS11_Result_exception_t case_Inr;
  }
  ;
}
FStar_Pervasives_either__uint64_t_Hacl_Impl_PKCS11_Result_exception_t;

typedef struct
Prims_dtuple2__FStar_Pervasives_either__uint64_t_Hacl_Impl_PKCS11_Result_exception_t_Hacl_Impl_PKCS11_DeviceModule_device_s
{
  FStar_Pervasives_either__uint64_t_Hacl_Impl_PKCS11_Result_exception_t fst;
  Hacl_Impl_PKCS11_DeviceModule_device snd;
}
Prims_dtuple2__FStar_Pervasives_either__uint64_t_Hacl_Impl_PKCS11_Result_exception_t_Hacl_Impl_PKCS11_DeviceModule_device;

extern Prims_dtuple2__FStar_Pervasives_either__uint64_t_Hacl_Impl_PKCS11_Result_exception_t_Hacl_Impl_PKCS11_DeviceModule_device
Hacl_Impl_Creation_GenKey__CKS_GenerateKey(
  Hacl_Impl_PKCS11_DeviceModule_device d,
  uint32_t hSession,
  uint32_t pMechanism,
  Prims_int pTemplate
);

#define __Hacl_Impl_Creation_GenKey_H_DEFINED
#endif
