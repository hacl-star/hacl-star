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

static Hacl_Impl_PKCS11_Result_exception_t
exceptionAdd(Hacl_Impl_PKCS11_Result_exception_t a, Hacl_Impl_PKCS11_Result_exception_t b)
{
  switch (a)
  {
    case Hacl_Impl_PKCS11_Result_CKR_OK:
      {
        return b;
      }
    default:
      {
        switch (b)
        {
          case Hacl_Impl_PKCS11_Result_CKR_OK:
            {
              return a;
            }
          default:
            {
              return b;
            }
        }
      }
  }
}

static uint32_t getAttributeType(Hacl_Impl_PKCS11_Internal_Attribute_attribute a)
{
  if (a.tag == Hacl_Impl_PKCS11_Internal_Attribute_CKA_CLASS)
  {
    return a.case_CKA_CLASS._type;
  }
  if (a.tag == Hacl_Impl_PKCS11_Internal_Attribute_CKA_TOKEN)
  {
    return a.case_CKA_TOKEN._type;
  }
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

static bool isAttributeReadOnly_(uint32_t attrType)
{
  Prims_int a = Lib_IntTypes_v(Lib_IntTypes_U32, Lib_IntTypes_SEC, (void *)attrType);
  if (a == (krml_checked_int_t)0)
  {
    return true;
  }
  return false;
}

static Hacl_Impl_PKCS11_Result_exception_t isAttributeReadOnly(uint32_t attrType)
{
  bool statusReadOnly = isAttributeReadOnly_(attrType);
  if (statusReadOnly)
  {
    return Hacl_Impl_PKCS11_Result_CKR_OK;
  }
  return Hacl_Impl_PKCS11_Result_CKR_ATTRIBUTE_READ_ONLY;
}

static void
isAttributeReadOnlyBuffer(
  Hacl_Impl_PKCS11_Internal_Attribute_attribute a,
  Hacl_Impl_PKCS11_Result_exception_t *b
)
{
  uint32_t t = getAttributeType(a);
  Hacl_Impl_PKCS11_Result_exception_t e = isAttributeReadOnly(t);
  Hacl_Impl_PKCS11_Result_exception_t oldException = b[0U];
  Hacl_Impl_PKCS11_Result_exception_t newException = exceptionAdd(oldException, e);
  b[0U] = newException;
}

static void
checkAttributes(uint32_t ulCount, Hacl_Impl_PKCS11_Internal_Attribute_attribute *pTemplate)
{
  Hacl_Impl_PKCS11_Result_exception_t bTest = Hacl_Impl_PKCS11_Result_CKR_OK;
  for (uint32_t i = (uint32_t)0U; i < ulCount; i = i + (uint32_t)1U)
  {
    isAttributeReadOnlyBuffer(pTemplate[i], &bTest);
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
  Hacl_Impl_PKCS11_Internal_Attribute_attribute *pTemplate,
  Hacl_Impl_PKCS11_Internal_Attribute_attributeD__uint32_t test
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

