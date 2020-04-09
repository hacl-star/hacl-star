module Hacl.PKCS11.Lemmas.ObjectTree

open Hacl.PKCS11.Types

(*
val lemmaSecretKeyIsObject: unit -> Lemma 
  (
    let attributesForSKO = getAttributesForType CKO_SECRET_KEY in 
    _attributesAllPresent 
