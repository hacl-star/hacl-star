module Hacl.PKCS11.Attributes.API

open FStar.Seq
open Hacl.PKCS11.Types
open Hacl.PKCS11.Lib
open Hacl.PKCS11.Lemmas

val _attributesAllPresent: toSearchSequence: seq _CK_ATTRIBUTE -> toFinds: seq _CK_ATTRIBUTE_TYPE -> Tot (r: bool
  {
    r == true ==> (forall (i: nat {i < Seq.length toFinds}). 
    contains (fun x -> x.aType = (index toFinds i)) toSearchSequence)
  }
)

let _attributesAllPresent toSearchSequence toFinds = 
  let __attributesAllPresent y toFind : r: bool 
  {r == true <==> contains (fun x -> x.aType = toFind) y} = 
    match find_l (fun x -> x.aType = toFind) y with 
    |None -> find_l_none_no_index y (fun x -> x.aType = toFind); false
    |Some _ -> lemmaFindLExistIfSome (fun x -> x.aType = toFind) y; true in   
  for_all (__attributesAllPresent toSearchSequence) toFinds 
