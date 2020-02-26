module Hacl.Impl.PKCS11.Session

open Hacl.Impl.PKCS11.Internal.Types
open Hacl.Impl.PKCS11.DeviceModule

open Hacl.Impl.PKCS11.Result

assume val getDeviceInitialised: d: device -> hSession: _CK_SESSION_HANDLE -> Tot bool

assume val sessionVerification: d: device -> hSession: _CK_SESSION_HANDLE -> Tot exception_t
