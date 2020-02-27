module Hacl.Impl.PKCS11.DeviceModule

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PKCS11.Internal.Types
open Hacl.Impl.PKCS11.KeyType

(* most probably the list of supported mechanisms should be a constant buffer, but because it should be an object independent from the implementation, I put it as a part of the device entity.
I.e. Device here is a set of metadata, that is not to be changed (like the list of supported mechanisms) and the description of the state - for example, the set of opened session.*)


(*
The EC (also related to ECDSA) key pair generation mechanism, denoted CKM_EC_KEY_PAIR_GEN or CKM_ECDSA_KEY_PAIR_GEN, is a key pair generation mechanism for EC.
The curve is taken from the attributes.
*)

noeq
type device = 
  |Device: 
    keyBufferLen: size_t -> 
    keys: Hacl.Impl.PKCS11.KeyType.key ->
    ulCountMechanisms: size_t ->
    listSupportedMechanisms: buffer _CK_MECHANISM_TYPE {length listSupportedMechanisms == uint_v ulCountMechanisms} ->
    ulCountCurves: size_t ->
    listSupportedCurves: buffer _CK_ULONG {length listSupportedCurves == uint_v ulCountCurves} ->
    device


assume val isCurveSupported: d: device -> curve: _HACL_Curve_ID ->  Tot bool