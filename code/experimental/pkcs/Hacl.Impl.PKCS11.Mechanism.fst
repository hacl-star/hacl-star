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
open Lib.IntTypes


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

assume val isMechanismCreation_: mechanism: _CK_MECHANISM_TYPE -> Tot bool

val isMechanismCreation: mechanism: _CK_MECHANISM_TYPE -> Tot exception_t

let isMechanismCreation mechanism =
  let creation = isMechanismCreation_ mechanism in 
  match creation with
  |true -> CKR_OK
  |false -> CKR_FUNCTION_FAILED
  

val mechanismCreationRequiredMemory: mechanism: _CK_MECHANISM_TYPE {isMechanismCreation_ mechanism} -> Tot size_t

let mechanismCreationRequiredMemory mechanism = 
  let mechanism = u32_to_UInt32 mechanism in 
  match mechanism with 
  |0ul -> (32ul)
  |_ -> (32ul)


val mechanismCreationHasEnoughMemory: d:device -> mechanism: _CK_MECHANISM_TYPE {isMechanismCreation_ mechanism} -> Tot (e: exception_t)

let mechanismCreationHasEnoughMemory d mechanism = 
  let requiredFreeSpace = mechanismCreationRequiredMemory mechanism in 
  if d.freeMemory >. requiredFreeSpace then CKR_OK
  else CKR_DEVICE_MEMORY

