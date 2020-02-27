module Hacl.Impl.PKCS11.External.DER

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes

open Hacl.Impl.PKCS11.Internal.Types
open Hacl.Impl.PKCS11.Result

open LowStar.Buffer
open Lib.RawIntTypes


assume val getCurveIdentifier: ulCount: size_t -> p: buffer uint8 {length p == uint_v ulCount /\ length p >=3} ->
  Stack ((e: exception_t) & (_HACL_Curve_ID))
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)
  

(* to change to another exception, the curve not supported is ONLY when the parsing was successful, but indeed not supported *)

(* https://en.wikipedia.org/wiki/X.690 *)
val parseEC_ANSI_962: ulCount: size_t -> p: buffer uint8 {length p == uint_v ulCount /\ length p >=3 } ->
  Stack ((e: exception_t) & (_HACL_Curve_ID))
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let parseEC_ANSI_962 ulCount p = 
  let expectedLength = to_u32 (index p 2ul) in 
  let sizeToCompare = ulCount - 2 in 
  if expectedLength <> sizeToCompare then 
    (|CKR_CURVE_NOT_SUPPORTED, 0ul|)
  else
    let objectIdentifier = to_u8 (index p 1ul) in 
      if objectIdentifier <> 9ul then 
	(|CKR_CURVE_NOT_SUPPORTED, 0ul|)
      else
	getCurveIdentifier ulCount p
