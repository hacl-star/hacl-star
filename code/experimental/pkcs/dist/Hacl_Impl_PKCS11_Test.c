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

extern Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t
Hacl_Impl_PKCS11_Internal_Attribute_getAttribute180(
  Hacl_Impl_PKCS11_Internal_Attribute_attribute *uu____733
);

#define Key 0

typedef uint8_t key_tags;

typedef Hacl_Impl_PKCS11_Internal_Object__object key;

extern bool
Hacl_Impl_PKCS11_DeviceModule_isCurveSupported(
  Hacl_Impl_PKCS11_DeviceModule_device d,
  uint32_t curve
);

extern Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t
Hacl_Impl_PKCS11_External_DER_getCurveIdentifier(uint32_t ulCount, uint8_t *p);

static Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t
parseEC_ANSI_962(uint32_t ulCount, uint8_t *p)
{
  uint32_t expectedLength = (uint32_t)p[2U];
  uint32_t sizeToCompare = ulCount - (uint32_t)2U;
  if (expectedLength != sizeToCompare)
  {
    return
      (
        (Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t){
          .fst = Hacl_Impl_PKCS11_Result_CKR_CURVE_NOT_SUPPORTED,
          .snd = (uint32_t)0U
        }
      );
  }
  uint8_t objectIdentifier = p[1U];
  if ((uint32_t)objectIdentifier != (uint32_t)9U)
  {
    return
      (
        (Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t){
          .fst = Hacl_Impl_PKCS11_Result_CKR_CURVE_NOT_SUPPORTED,
          .snd = (uint32_t)0U
        }
      );
  }
  return Hacl_Impl_PKCS11_External_DER_getCurveIdentifier(ulCount, p);
}

static Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t
isAttributeEC_PARAMCorrect(
  Hacl_Impl_PKCS11_DeviceModule_device d,
  Hacl_Impl_PKCS11_Internal_Attribute_attribute a
)
{
  uint32_t ulCount;
  if (a.tag == Hacl_Impl_PKCS11_Internal_Attribute_CKA_EC_PARAMS)
  {
    ulCount = a.case_CKA_EC_PARAMS.ulValueLen;
  }
  else
  {
    ulCount = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
  }
  uint32_t ite0;
  if (a.tag == Hacl_Impl_PKCS11_Internal_Attribute_CKA_EC_PARAMS)
  {
    ite0 = a.case_CKA_EC_PARAMS.ulValueLen;
  }
  else
  {
    ite0 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
  }
  void **ite;
  if (a.tag == Hacl_Impl_PKCS11_Internal_Attribute_CKA_EC_PARAMS)
  {
    ite = a.case_CKA_EC_PARAMS.pValue;
  }
  else
  {
    ite = KRML_EABORT(void **, "unreachable (pattern matches are exhaustive in F*)");
  }
  Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t
  scrut = parseEC_ANSI_962(ite0, (uint8_t *)ite);
  Hacl_Impl_PKCS11_Result_exception_t exc = scrut.fst;
  uint32_t curveIdentifier = scrut.snd;
  switch (exc)
  {
    case Hacl_Impl_PKCS11_Result_CKR_OK:
      {
        bool curveSupported = Hacl_Impl_PKCS11_DeviceModule_isCurveSupported(d, curveIdentifier);
        if (curveSupported == true)
        {
          return
            (
              (Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t){
                .fst = Hacl_Impl_PKCS11_Result_CKR_OK,
                .snd = curveIdentifier
              }
            );
        }
        if (curveSupported == false)
        {
          return
            (
              (Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t){
                .fst = Hacl_Impl_PKCS11_Result_CKR_CURVE_NOT_SUPPORTED,
                .snd = curveIdentifier
              }
            );
        }
        return
          (
            (Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t){
              .fst = exc,
              .snd = curveIdentifier
            }
          );
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static Hacl_Impl_PKCS11_Result_exception_t
mechanismEnforcedAttributeCheck(
  Hacl_Impl_PKCS11_DeviceModule_device d,
  uint32_t mechanism,
  Hacl_Impl_PKCS11_Internal_Attribute_attribute *pTemplate
)
{
  uint32_t mechanism1 = mechanism;
  switch (mechanism1)
  {
    case 0U:
      {
        Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t
        scrut = Hacl_Impl_PKCS11_Internal_Attribute_getAttribute180(pTemplate);
        Hacl_Impl_PKCS11_Result_exception_t exc = scrut.fst;
        uint32_t indexAttribute = scrut.snd;
        switch (exc)
        {
          case Hacl_Impl_PKCS11_Result_CKR_OK:
            {
              Hacl_Impl_PKCS11_Internal_Attribute_attribute attr = pTemplate[indexAttribute];
              Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t
              scrut0 = isAttributeEC_PARAMCorrect(d, attr);
              return scrut0.fst;
            }
          default:
            {
              return exc;
            }
        }
        break;
      }
    default:
      {
        return Hacl_Impl_PKCS11_Result_CKR_OK;
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
  Hacl_Impl_PKCS11_Internal_Attribute_attribute *parsedAttributes = scrut.snd;
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
  Hacl_Impl_PKCS11_Result_exception_t
  mechanismCheckException = mechanismEnforcedAttributeCheck(d, pMechanism, parsedAttributes);
  switch (mechanismCheckException)
  {
    case Hacl_Impl_PKCS11_Result_CKR_OK:
      {
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
    default:
      {
        return
          (
            (Prims_dtuple2__Hacl_Impl_PKCS11_Result_exception_t_uint32_t){
              .fst = mechanismCheckException,
              .snd = (uint32_t)0U
            }
          );
      }
  }
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

