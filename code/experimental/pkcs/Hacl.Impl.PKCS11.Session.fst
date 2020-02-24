module Hacl.Impl.PKCS11.Session

open Hacl.Impl.PKCS11.Internal.Types
open Hacl.Impl.PKCS11.DeviceModule

assume val getDeviceInitialised: d: device -> hSession: _CK_SESSION_HANDLE -> Tot bool
