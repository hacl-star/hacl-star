module Hacl.Impl.PKCS11.Parsing

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes

open Hacl.Impl.PKCS11.Internal.Attribute
open Hacl.Impl.PKCS11.Internal.Types
open Hacl.Impl.PKCS11.Result

(* totally wrong, i know, just an example.
The idealistic is to check whether it is void or not, then to check whether they between each other are equal. I have no idea how to do it for now, so. 

*)
val compareT: t0: Type0 -> t1: Type0 -> Tot bool

let compareT t0 t1 = 
  match t0 with 
  |void -> match t1 with |void -> true |_ -> false
  |_ -> false
  

val parseAttribute: #t: Type0 -> attributeD #t -> 
  Stack (result attribute)
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let parseAttribute #t a = 
  let attrT = uint_v (a._type) in 
  match attrT with 
  | 0 -> 
    let expectedType = void_t (typeID_type attrT) in 
    let expectedLen = lenAttribute a._type in 
    if not (compareT expectedType t) then 
      Inr CKR_ARGUMENTS_BAD
    else if not (eq expectedLen a.ulValueLen) then
      Inr CKR_ARGUMENTS_BAD
    else  
      Inl (CKA_CLASS a._type  a.pValue a.ulValueLen)
  | _ -> Inr CKR_ARGUMENTS_BAD
    
