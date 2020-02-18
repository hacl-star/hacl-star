module Hacl.Impl.PKCS11.Creation.GenKey

open Hacl.Impl.PKCS11.Internal.Types
open Hacl.Impl.PKCS11.Internal.Attribute
open Hacl.Impl.PKCS11.DeviceModule

open Hacl.Impl.PKCS11.Result

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open LowStar.Buffer

(* C_GenerateKey generates a secret key or set of domain parameters, creating a new object. 
hSession is the session’s handle; 
pMechanism points to the generation mechanism; 
pTemplate points to the template for the new key or set of domain parameters; 
ulCount is the number of attributes in the template; 
phKey points to the location that receives the handle of the new key or set of domain parameters.

If the generation mechanism is for domain parameter generation, the CKA_CLASS attribute will have the value CKO_DOMAIN_PARAMETERS; otherwise, it will have the value CKO_SECRET_KEY.

Since the type of key or domain parameters to be generated is implicit in the generation mechanism, the template does not need to supply a key type.  If it does supply a key type which is inconsistent with the generation mechanism, C_GenerateKey fails and returns the error code CKR_TEMPLATE_INCONSISTENT.  The CKA_CLASS attribute is treated similarly.

If a call to C_GenerateKey cannot support the precise template supplied to it, it will fail and return without creating an object.

The object created by a successful call to C_GenerateKey will have its CKA_LOCAL attribute set to CK_TRUE.

Return values: CKR_ARGUMENTS_BAD, 
CKR_ATTRIBUTE_READ_ONLY -> val isAttributeReadOnly: _CK_ATTRIBUTE_TYPE -> Tot (r: exception_t {CKR_OK? r \/ CKR_ATTRIBUTE_READ_ONLY? r})
CKR_ATTRIBUTE_TYPE_INVALID, CKR_ATTRIBUTE_VALUE_INVALID, CKR_CRYPTOKI_NOT_INITIALIZED, CKR_CURVE_NOT_SUPPORTED, CKR_DEVICE_ERROR, CKR_DEVICE_MEMORY, CKR_DEVICE_REMOVED, CKR_FUNCTION_CANCELED, CKR_FUNCTION_FAILED, CKR_GENERAL_ERROR, CKR_HOST_MEMORY, CKR_MECHANISM_INVALID, CKR_MECHANISM_PARAM_INVALID, CKR_OK, CKR_OPERATION_ACTIVE, CKR_PIN_EXPIRED, CKR_SESSION_CLOSED, CKR_SESSION_HANDLE_INVALID, CKR_SESSION_READ_ONLY, CKR_TEMPLATE_INCOMPLETE, CKR_TEMPLATE_INCONSISTENT, CKR_TOKEN_WRITE_PROTECTED, CKR_USER_NOT_LOGGED_IN.

*)


val _CKS_GenerateKey: 
  d: device -> 
  hSession: _CK_SESSION_HANDLE ->
  pMechanism: _CK_MECHANISM_TYPE ->
  ulCount: size_t -> 
  pTemplate: buffer attribute {length pTemplate = uint_v ulCount} -> 
  Stack 
    ((handler: result nat) & (device))
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)


let _CKS_GenerateKey d hSession pMechanism ulCould pTemplate = 
  let testCall = checkAttributes ulCould pTemplate in 

  (|Inl 0, d|) 
