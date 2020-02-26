module Hacl.Impl.PKCS11.Session

open Hacl.Impl.PKCS11.Internal.Types
open Hacl.Impl.PKCS11.DeviceModule

open Hacl.Impl.PKCS11.Result

assume val getDeviceInitialised: d: device -> hSession: _CK_SESSION_HANDLE -> Tot bool

val sessionVerification: d: device -> hSession: _CK_SESSION_HANDLE -> Tot (e: exception_t
  {
    CKR_OK? e <==> getDeviceInitialised d hSession /\
    CKR_CRYPTOKI_NOT_INITIALIZED? e <==> not (getDeviceInitialised d hSession)
  }) 

let sessionVerification d hSession = 
  let deviceInit = getDeviceInitialised d hSession in 
  if not (deviceInit) then 
    CKR_CRYPTOKI_NOT_INITIALIZED
  else
    CKR_OK
