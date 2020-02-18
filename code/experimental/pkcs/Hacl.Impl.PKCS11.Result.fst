module Hacl.Impl.PKCS11.Result

open Hacl.Impl.PKCS11.Internal.Types


type exception_t = 
  | CKR_OK
  | CKR_ARGUMENTS_BAD 
  | CKR_ATTRIBUTE_READ_ONLY 
  (*If the supplied template specifies a value for an invalid attribute, then the attempt should fail with the error code CKR_ATTRIBUTE_TYPE_INVALID.  An attribute is valid if it is either one of the attributes described in the Cryptoki specification or an additional vendor-specific attribute supported by the library and token. *)
  | CKR_ATTRIBUTE_TYPE_INVALID
  | CKR_ATTRIBUTE_VALUE_INVALID 
  | CKR_CRYPTOKI_NOT_INITIALIZED 
  | CKR_CURVE_NOT_SUPPORTED
  | CKR_DEVICE_ERROR 
  | CKR_DEVICE_MEMORY 
  | CKR_DEVICE_REMOVED 
  | CKR_FUNCTION_CANCELED 
  | CKR_FUNCTION_FAILED 
  | CKR_GENERAL_ERROR 
  | CKR_HOST_MEMORY 
  | CKR_MECHANISM_INVALID 
  | CKR_MECHANISM_PARAM_INVALID 
  | CKR_OPERATION_ACTIVE 
  | CKR_PIN_EXPIRED 
  | CKR_SESSION_CLOSED 
  | CKR_SESSION_HANDLE_INVALID 
  | CKR_SESSION_READ_ONLY 
  | CKR_TEMPLATE_INCOMPLETE 
  | CKR_TEMPLATE_INCONSISTENT 
  | CKR_TOKEN_WRITE_PROTECTED 
  | CKR_USER_NOT_LOGGED_IN
  | CKR_JUST_FOR_TEST

type result 'a = either 'a exception_t

(* The function takes two exceptions and returns one out of them according to the rule:
if one of the expections is CKR_OK, but not the second -> return the second
if none of them are CKR_OK, return any
*)

val exceptionAdd: a: exception_t -> b: exception_t -> Tot (e: exception_t
  {
    if CKR_OK? a then e == b else
    if CKR_OK? b then e == a else
    e == b
  }
)


let exceptionAdd a b = 
  match a with
  |CKR_OK -> b
  |_ -> 
    match b with
    |CKR_OK -> a
    |_ -> b
