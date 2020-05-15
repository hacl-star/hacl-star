module Hacl.PKCS11.Lemmas.LowLevel

open FStar.Seq


assume val lemmaFromListToSequence: #a: Type0 
  -> l: list a 
  -> Lemma
  (ensures (
    forall (i: nat). i < List.Tot.length l ==>
    index (seq_of_list l) i == List.Tot.index l i)
  )


assume val snocSlice: #a: Type0 -> s: seq a -> e: a -> Lemma
	(
		let s1 = snoc s in 
		(forall (i: nat). i < length s ==> index s i == index s1 i) /\ 
		index s1 (length s1 - 1) == e

	)