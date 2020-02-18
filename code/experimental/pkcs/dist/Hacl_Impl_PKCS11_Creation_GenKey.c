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


#include "Hacl_Impl_PKCS11_Creation_GenKey.h"

extern void
Hacl_Impl_PKCS11_Internal_Attribute_isAttributeReadOnlyBuffer(
  Hacl_Impl_PKCS11_Internal_Attribute_attribute uu____339,
  Hacl_Impl_PKCS11_Result_exception_t *b
);

static void
checkAttributes(uint32_t ulCount, Hacl_Impl_PKCS11_Internal_Attribute_attribute *pTemplate)
{
  Hacl_Impl_PKCS11_Result_exception_t bTest = Hacl_Impl_PKCS11_Result_CKR_OK;
  for (uint32_t i = (uint32_t)0U; i < ulCount; i = i + (uint32_t)1U)
  {
    Hacl_Impl_PKCS11_Internal_Attribute_isAttributeReadOnlyBuffer(pTemplate[i], &bTest);
  }
}

#define Key 0

typedef uint8_t key_tags;

typedef Hacl_Impl_PKCS11_Internal_Object__object key;

Prims_dtuple2__FStar_Pervasives_either__Prims_int_Hacl_Impl_PKCS11_Result_exception_t_Hacl_Impl_PKCS11_DeviceModule_device
Hacl_Impl_PKCS11_Creation_GenKey__CKS_GenerateKey(
  Hacl_Impl_PKCS11_DeviceModule_device d,
  uint32_t hSession,
  uint32_t pMechanism,
  uint32_t ulCould,
  Hacl_Impl_PKCS11_Internal_Attribute_attribute *pTemplate
)
{
  checkAttributes(ulCould, pTemplate);
  return
    (
      (Prims_dtuple2__FStar_Pervasives_either__Prims_int_Hacl_Impl_PKCS11_Result_exception_t_Hacl_Impl_PKCS11_DeviceModule_device){
        .fst = { .tag = FStar_Pervasives_Inl, { .case_Inl = (krml_checked_int_t)0 } },
        .snd = d
      }
    );
}

