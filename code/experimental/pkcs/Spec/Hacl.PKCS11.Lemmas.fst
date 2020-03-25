module Hacl.PKCS11.Lemmas

open FStar.Seq


val lemmaFindLExistIfSome: #a: Type -> f: (a -> bool) -> s: seq a -> Lemma
  (requires
    (Some? (find_l f s)))
  (ensures (exists (a: nat {a < Seq.length s}). f (index s a)))
  (decreases (Seq.length s))


let rec lemmaFindLExistIfSome #a f s = 
  if length s = 0 then ()
  else if length s = 1 then () 
  else
    if f (head s) then ()
    else 
      lemmaFindLExistIfSome f (tail s)
