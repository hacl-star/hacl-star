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


#include "Hacl_Impl_PKCS11_Test.h"

static bool uu___is_CKR_OK(Hacl_Impl_PKCS11_Result_exception_t projectee)
{
  switch (projectee)
  {
    case Hacl_Impl_PKCS11_Result_CKR_OK:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

typedef struct
dtuple2__Hacl_Impl_PKCS11_Result_exception_t__Hacl_Impl_PKCS11_Internal_Attribute_attribute__s
{
  Hacl_Impl_PKCS11_Result_exception_t fst;
  Hacl_Impl_PKCS11_Internal_Attribute_attribute *snd;
}
dtuple2__Hacl_Impl_PKCS11_Result_exception_t__Hacl_Impl_PKCS11_Internal_Attribute_attribute_;

extern dtuple2__Hacl_Impl_PKCS11_Result_exception_t__Hacl_Impl_PKCS11_Internal_Attribute_attribute_
Hacl_Impl_PKCS11_Parsing_parseAttributes(
  uint32_t ulCount,
  Hacl_Impl_PKCS11_Internal_Attribute_attributeD *pTemplate
);

#define Key 0

typedef uint8_t key_tags;

typedef Hacl_Impl_PKCS11_Internal_Object__object key;

extern bool
Hacl_Impl_PKCS11_Session_getDeviceInitialised(
  Hacl_Impl_PKCS11_DeviceModule_device d,
  uint32_t hSession
);

static Hacl_Impl_PKCS11_Result_exception_t
sessionVerification(Hacl_Impl_PKCS11_DeviceModule_device d, uint32_t hSession)
{
  bool deviceInit = Hacl_Impl_PKCS11_Session_getDeviceInitialised(d, hSession);
  if (!deviceInit)
  {
    return Hacl_Impl_PKCS11_Result_CKR_CRYPTOKI_NOT_INITIALIZED;
  }
  return Hacl_Impl_PKCS11_Result_CKR_OK;
}

static Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t
_CKS_GenerateKey_(Hacl_Impl_PKCS11_DeviceModule_device d)
{
  return
    (
      (Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t){
        .fst = Hacl_Impl_PKCS11_Result_CKR_OK,
        .snd = (uint32_t)0U
      }
    );
}

static Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t
_CKS_GenerateKey(
  Hacl_Impl_PKCS11_DeviceModule_device d,
  uint32_t hSession,
  uint32_t pMechanism,
  uint32_t ulCount,
  Hacl_Impl_PKCS11_Internal_Attribute_attributeD *pTemplate
)
{
  dtuple2__Hacl_Impl_PKCS11_Result_exception_t__Hacl_Impl_PKCS11_Internal_Attribute_attribute_
  scrut = Hacl_Impl_PKCS11_Parsing_parseAttributes(ulCount, pTemplate);
  Hacl_Impl_PKCS11_Result_exception_t exceptionParsing = scrut.fst;
  if (!uu___is_CKR_OK(exceptionParsing))
  {
    return
      (
        (Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t){
          .fst = exceptionParsing,
          .snd = (uint32_t)0U
        }
      );
  }
  Hacl_Impl_PKCS11_Result_exception_t sessionException = sessionVerification(d, hSession);
  if (!uu___is_CKR_OK(sessionException))
  {
    return
      (
        (Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t){
          .fst = sessionException,
          .snd = (uint32_t)0U
        }
      );
  }
  Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t scrut0 = _CKS_GenerateKey_(d);
  Hacl_Impl_PKCS11_Result_exception_t exceptionMain = scrut0.fst;
  uint32_t handler = scrut0.snd;
  return
    (
      (Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t){
        .fst = exceptionMain,
        .snd = handler
      }
    );
}

Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t
Hacl_Impl_PKCS11_Test_test(
  Hacl_Impl_PKCS11_DeviceModule_device d,
  uint32_t hSession,
  uint32_t pMechanism,
  uint32_t ulCount,
  Hacl_Impl_PKCS11_Internal_Attribute_attributeD *pTemplate
)
{
  return _CKS_GenerateKey(d, hSession, pMechanism, ulCount, pTemplate);
}

