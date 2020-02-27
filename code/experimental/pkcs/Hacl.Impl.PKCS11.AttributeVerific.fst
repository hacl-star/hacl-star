module Hacl.Impl.PKCS11.AttributeVerific

open Lib.IntTypes
open Hacl.Impl.PKCS11.Internal.Types

open Hacl.Impl.PKCS11.Result
open Hacl.Impl.PKCS11.External.DER

open Hacl.Impl.PKCS11.Internal.Attribute
open Hacl.Impl.PKCS11.DeviceModule

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.RawIntTypes
open LowStar.Buffer


val isAttributeEC_PARAMCorrect: d: device ->  a: attribute {CKA_EC_PARAMS? a} -> Stack (((e: exception_t) & (_HACL_Curve_ID)))
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let isAttributeEC_PARAMCorrect d a = 
  let ulCount = CKA_EC_PARAMS?.ulValueLen a in 
  let (|exc, curveIdentifier|) = parseEC_ANSI_962 (CKA_EC_PARAMS?.ulValueLen a) (CKA_EC_PARAMS?.pValue a) in  
  match exc with 
  |CKR_OK -> 
    let curveSupported = isCurveSupported d curveIdentifier in 
    match curveSupported with 
      |true -> (|CKR_OK, curveIdentifier|)
      |false -> (|CKR_CURVE_NOT_SUPPORTED, curveIdentifier|)
  | _ -> (|exc, curveIdentifier|)
  


val checkAttributes: ulCount: size_t -> pTemplate: buffer attribute{length pTemplate = uint_v ulCount} -> Stack unit
  (requires fun h -> live h pTemplate)
  (ensures fun h0 _ h1 -> True)

let checkAttributes ulCount pTemplate = 
  push_frame();
  [@inline_let]
  let okException = CKR_OK in 
  let bTest = LowStar.Buffer.alloca okException (normalize_term 1ul) in  
  C.Loops.for 0ul ulCount (fun h i -> True) (fun i ->  isAttributeReadOnlyBuffer (index pTemplate i) bTest);
  pop_frame()
