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

#ifndef __Hacl_Impl_PKCS11_Test_H
#define __Hacl_Impl_PKCS11_Test_H




#define Hacl_Impl_PKCS11_Internal_Types_CK_ULONG 0
#define Hacl_Impl_PKCS11_Internal_Types_CK_BOOL 1

typedef uint8_t Hacl_Impl_PKCS11_Internal_Types_void;

#define Hacl_Impl_PKCS11_Result_CKR_OK 0
#define Hacl_Impl_PKCS11_Result_CKR_ARGUMENTS_BAD 1
#define Hacl_Impl_PKCS11_Result_CKR_ATTRIBUTE_READ_ONLY 2
#define Hacl_Impl_PKCS11_Result_CKR_ATTRIBUTE_TYPE_INVALID 3
#define Hacl_Impl_PKCS11_Result_CKR_ATTRIBUTE_VALUE_INVALID 4
#define Hacl_Impl_PKCS11_Result_CKR_CRYPTOKI_NOT_INITIALIZED 5
#define Hacl_Impl_PKCS11_Result_CKR_CURVE_NOT_SUPPORTED 6
#define Hacl_Impl_PKCS11_Result_CKR_DEVICE_ERROR 7
#define Hacl_Impl_PKCS11_Result_CKR_DEVICE_MEMORY 8
#define Hacl_Impl_PKCS11_Result_CKR_DEVICE_REMOVED 9
#define Hacl_Impl_PKCS11_Result_CKR_FUNCTION_CANCELED 10
#define Hacl_Impl_PKCS11_Result_CKR_FUNCTION_FAILED 11
#define Hacl_Impl_PKCS11_Result_CKR_GENERAL_ERROR 12
#define Hacl_Impl_PKCS11_Result_CKR_HOST_MEMORY 13
#define Hacl_Impl_PKCS11_Result_CKR_MECHANISM_INVALID 14
#define Hacl_Impl_PKCS11_Result_CKR_MECHANISM_PARAM_INVALID 15
#define Hacl_Impl_PKCS11_Result_CKR_OPERATION_ACTIVE 16
#define Hacl_Impl_PKCS11_Result_CKR_PIN_EXPIRED 17
#define Hacl_Impl_PKCS11_Result_CKR_SESSION_CLOSED 18
#define Hacl_Impl_PKCS11_Result_CKR_SESSION_HANDLE_INVALID 19
#define Hacl_Impl_PKCS11_Result_CKR_SESSION_READ_ONLY 20
#define Hacl_Impl_PKCS11_Result_CKR_TEMPLATE_INCOMPLETE 21
#define Hacl_Impl_PKCS11_Result_CKR_TEMPLATE_INCONSISTENT 22
#define Hacl_Impl_PKCS11_Result_CKR_TOKEN_WRITE_PROTECTED 23
#define Hacl_Impl_PKCS11_Result_CKR_USER_NOT_LOGGED_IN 24
#define Hacl_Impl_PKCS11_Result_CKR_JUST_FOR_TEST 25

typedef uint8_t Hacl_Impl_PKCS11_Result_exception_t;

typedef struct Hacl_Impl_PKCS11_Internal_Attribute_attributeD_s
{
  uint32_t _type;
  Hacl_Impl_PKCS11_Internal_Types_void *pValue;
  uint32_t ulValueLen;
}
Hacl_Impl_PKCS11_Internal_Attribute_attributeD;

#define Hacl_Impl_PKCS11_Internal_Attribute_CKA_CLASS 0
#define Hacl_Impl_PKCS11_Internal_Attribute_CKA_TOKEN 1
#define Hacl_Impl_PKCS11_Internal_Attribute_CKA_EC_PARAMS 2

typedef uint8_t Hacl_Impl_PKCS11_Internal_Attribute_attribute_tags;

typedef struct Hacl_Impl_PKCS11_Internal_Attribute_attribute_s
{
  Hacl_Impl_PKCS11_Internal_Attribute_attribute_tags tag;
  union {
    struct 
    {
      uint32_t _type;
      void **pValue;
      uint32_t ulValueLen;
    }
    case_CKA_CLASS;
    struct 
    {
      uint32_t _type;
      void **pValue;
      uint32_t ulValueLen;
    }
    case_CKA_TOKEN;
    struct 
    {
      uint32_t _type;
      void **pValue;
      uint32_t ulValueLen;
    }
    case_CKA_EC_PARAMS;
  }
  ;
}
Hacl_Impl_PKCS11_Internal_Attribute_attribute;

typedef struct Hacl_Impl_PKCS11_Internal_Object__object_s
{
  uint32_t id;
  uint32_t dataLen;
  uint8_t *data;
  Hacl_Impl_PKCS11_Internal_Attribute_attribute attributes_;
}
Hacl_Impl_PKCS11_Internal_Object__object;

typedef struct Hacl_Impl_PKCS11_DeviceModule_device_s
{
  uint32_t keyBufferLen;
  Hacl_Impl_PKCS11_Internal_Object__object keys;
  uint32_t ulCountMechanisms;
  uint32_t *listSupportedMechanisms;
  uint32_t ulCountCurves;
  uint32_t *listSupportedCurves;
}
Hacl_Impl_PKCS11_DeviceModule_device;

typedef struct Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t_s
{
  Hacl_Impl_PKCS11_Result_exception_t fst;
  uint32_t snd;
}
Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t;

Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t
Hacl_Impl_PKCS11_Test_test(
  Hacl_Impl_PKCS11_DeviceModule_device d,
  uint32_t hSession,
  uint32_t pMechanism,
  uint32_t ulCount,
  Hacl_Impl_PKCS11_Internal_Attribute_attributeD *pTemplate
);

#define __Hacl_Impl_PKCS11_Test_H_DEFINED
#endif
