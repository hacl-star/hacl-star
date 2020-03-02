module Hacl.Impl.PKCS11.Creation.GenKey

open Hacl.Impl.PKCS11.Internal.Types
open Hacl.Impl.PKCS11.Internal.Attribute
open Hacl.Impl.PKCS11.DeviceModule
open Hacl.Impl.PKCS11.Session

open Hacl.Impl.PKCS11.Mechanism

open Hacl.Impl.PKCS11.Result
open Hacl.Impl.PKCS11.Parsing

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

CKR_ATTRIBUTE_READ_ONLY:  val isAttributeReadOnly: _CK_ATTRIBUTE_TYPE -> Tot (r: exception_t {CKR_OK? r \/ CKR_ATTRIBUTE_READ_ONLY? r})

CKR_ATTRIBUTE_TYPE_INVALID - see parsing
CKR_ATTRIBUTE_VALUE_INVALID - see parsing

CKR_CRYPTOKI_NOT_INITIALIZED:  CKR_CRYPTOKI_NOT_INITIALIZED? e <==> not (getDeviceInitialised d hSession)

CKR_CURVE_NOT_SUPPORTED - in mechanism generation if the mechanism is using a curve to generate a key pair, but curve is not supported (?)

CKR_DEVICE_ERROR: Some problem has occurred with the token and/or slot - not used in the model

CKR_DEVICE_MEMORY: The token does not have sufficient memory to perform the requested function.

CKR_DEVICE_REMOVED: The token was removed from its slot during the execution of the function.


, CKR_FUNCTION_CANCELED, CKR_FUNCTION_FAILED, 
CKR_GENERAL_ERROR, CKR_HOST_MEMORY, CKR_MECHANISM_INVALID, CKR_MECHANISM_PARAM_INVALID, CKR_OK, CKR_OPERATION_ACTIVE, CKR_PIN_EXPIRED, CKR_SESSION_CLOSED, CKR_SESSION_HANDLE_INVALID, CKR_SESSION_READ_ONLY, CKR_TEMPLATE_INCOMPLETE, CKR_TEMPLATE_INCONSISTENT, CKR_TOKEN_WRITE_PROTECTED, CKR_USER_NOT_LOGGED_IN.

*)



val _CKS_GenerateKey_: 
  d: device -> 
  hSession: _CK_SESSION_HANDLE {getDeviceInitialised d hSession} ->
  pMechanism: _CK_MECHANISM_TYPE ->
  ulCount: size_t -> 
  pTemplate: buffer attribute {length pTemplate = uint_v ulCount} -> 
  Stack (
    (exp: exception_t) & (_CK_OBJECT_HANDLE))
      (requires fun h -> True)
      (ensures fun h0 _ h1 -> True)

let _CKS_GenerateKey_ d hSession pMechanism ulCould pTemplate = 
  (|CKR_OK, (u32 0)|) 


val _CKS_GenerateKey: 
  d: device -> 
  hSession: _CK_SESSION_HANDLE -> 
  pMechanism: _CK_MECHANISM_TYPE -> 
  ulCount: size_t -> 
  pTemplate: buffer attributeD {length pTemplate = uint_v ulCount} -> 
  Stack (
    (exp: exception_t) & (_CK_OBJECT_HANDLE))
  (requires fun h -> live h pTemplate)
  (ensures fun h0 _ h1 -> True)


let _CKS_GenerateKey d hSession pMechanism ulCount pTemplate = 
  push_frame();
  let mechanismCreation = isMechanismCreation pMechanism in 
  match mechanismCreation with 
  |CKR_OK -> begin
    let isEnoughMemory = mechanismCreationHasEnoughMemory d pMechanism in 
    match isEnoughMemory with 
    |CKR_OK -> begin
    let (|exceptionParsing, parsedAttributes|) = parseAttributes ulCount pTemplate in 
    if not (CKR_OK? exceptionParsing) then 
      begin 
	pop_frame();
	(|exceptionParsing, (u32 0)|)
      end
    else
    let sessionException = sessionVerification d hSession in 
    if not (CKR_OK? sessionException) then 
      begin 
	pop_frame();
	(|sessionException, (u32 0)|)
	end
    else 
      begin
	let mechanismCheckException = mechanismEnforcedAttributeCheck d pMechanism parsedAttributes in 
	match mechanismCheckException with 
	|CKR_OK -> 
	  let (|exceptionMain, handler|) =  _CKS_GenerateKey_ d hSession pMechanism ulCount parsedAttributes in
	  pop_frame();
	  (|exceptionMain, handler|)
	|_ -> 
	  pop_frame(); 
	  (|mechanismCheckException, (u32 0)|)
      end
    end
    |_ ->  pop_frame(); (|isEnoughMemory, (u32 0)|)
    end
 |_ ->pop_frame(); (|mechanismCreation, (u32 0)|)
