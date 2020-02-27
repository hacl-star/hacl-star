module Hacl.Impl.PKCS11.Mechanism

open Hacl.Impl.PKCS11.Internal.Types
open Hacl.Impl.PKCS11.Result
open Hacl.Impl.PKCS11.DeviceModule

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Hacl.Impl.PKCS11.Internal.Attribute
open Hacl.Impl.PKCS11.AttributeVerific

open Lib.RawIntTypes
open LowStar.Buffer


val mechanismEnforcedAttributeCheck: d: device -> mechanism: _CK_MECHANISM_TYPE -> pTemplate: buffer attribute -> Stack exception_t
  (requires fun h -> live h pTemplate)
  (ensures fun h0 _ h1 -> True)


let mechanismEnforcedAttributeCheck d mechanism pTemplate = 
  let mechanism = u32_to_UInt32 mechanism in 
  match mechanism with 
  |0ul -> 
    begin
    let (|exc, indexAttribute|) = getAttribute180 pTemplate in 
    match exc with 
      |CKR_OK -> 
	assume (UInt32.v indexAttribute < length pTemplate);
	let attr = index pTemplate indexAttribute in 
	assume (CKA_EC_PARAMS? attr);
	let (|expEC, curveID|) =  isAttributeEC_PARAMCorrect d attr in 
	expEC
      | _ -> exc
    end  
  |_ -> CKR_OK
