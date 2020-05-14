module Hacl.PKCS11.Attributes.API

open FStar.Seq
open Hacl.PKCS11.Types
open Hacl.PKCS11.Lib
open Hacl.PKCS11.Lemmas


#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

let attributesAllPresent (s: seq _CK_ATTRIBUTE) (f: seq _CK_ATTRIBUTE_TYPE) : Type0 = 
  forall (i: nat). i< Seq.length f ==> contains (fun x -> x.aType = (index f i)) s
  

val _attributesAllPresent: toSearchSequence: seq _CK_ATTRIBUTE -> toFind: seq _CK_ATTRIBUTE_TYPE -> Tot (r: bool
  {
    r == true <==> attributesAllPresent toSearchSequence toFind
  }
)

let _attributesAllPresent toSearchSequence toFind = 
  let __attributesAllPresent y toFind : r: bool 
  {r == true <==> contains (fun x -> x.aType = toFind) y} = 
    match find_l (fun x -> x.aType = toFind) y with 
    |None -> find_l_none_no_index y (fun x -> x.aType = toFind); false
    |Some _ -> lemmaFindLExistIfSome (fun x -> x.aType = toFind) y; true in  
    
  let r = for_all (__attributesAllPresent toSearchSequence) toFind in 
  let z s f = forall (i: nat). i< Seq.length f ==> contains (fun x -> x.aType = (index f i)) s in 
  r

