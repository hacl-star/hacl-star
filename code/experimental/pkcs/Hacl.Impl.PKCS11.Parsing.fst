module Hacl.Impl.PKCS11.Parsing

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes

open Hacl.Impl.PKCS11.Internal.Attribute
open Hacl.Impl.PKCS11.Internal.Types
open Hacl.Impl.PKCS11.Result

open LowStar.Buffer

(* totally wrong, i know, just an example.
The idealistic is to check whether it is void or not, then to check whether they between each other are equal. I have no idea how to do it for now, so. 
*)

(*
  Exceptions: 
  CKR_ATTRIBUTE_TYPE_INVALID -> in parsing the main match to have a value out of possible
  CKR_ATTRIBUTE_VALUE_INVALID -> in the second match if the checkes are not satisfied (i.e. can't cast to the attribute)


NB: I am NOT sure that this code is critical to the work itself, it's more about intercommunication.


*)


(*
  For the eq types -> if eq t0 t1 then true
  For not eq types -> if t0 == t1 (i.e. the same type), even if by hand

*)
assume val compareT: t0: Type0 -> t1: Type0 -> Tot (t: bool {t0 == t1})


assume val parseAttribute: #t: Type0 -> a: attributeD #t -> 
  StackInline (exception_t & attribute)
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

assume val parseAttributes: #t: Type0 -> ulCount: size_t -> pTemplate: buffer (attributeD #t)  {length pTemplate = uint_v ulCount} -> 
  StackInline 
    (e: exception_t 
      {CKR_ATTRIBUTE_TYPE_INVALID? e \/ CKR_ATTRIBUTE_VALUE_INVALID? e \/ CKR_ARGUMENTS_BAD? e} & buffer attribute)
  (requires fun h -> live h pTemplate)
  (ensures fun h0 _ h1 -> True)

