module Hacl.PKCS11.Lemmas.LowLevel

open FStar.Seq


assume val lemmaFromListToSequence: #a: Type0 
  -> l: list a 
  -> Lemma
  (ensures (
    forall (i: nat). i < List.Tot.length l ==>
    index (seq_of_list l) i == List.Tot.index l i)
  )
