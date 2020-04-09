module Hacl.PKCS11.Lib

open FStar.Seq


val for_all2: #a: eqtype -> #b: eqtype -> f: (a -> b -> bool) -> s: seq a -> s1: seq b {Seq.length s = Seq.length s1} -> 
  Tot bool (decreases (Seq.length s))


let rec for_all2 #a #b f s s1 = 
  match length s with
    | 0 -> true
    | _ -> 
      if f (head s) (head s1) then 
	for_all2 f (tail s) (tail s1)
      else 
	false


assume val map: #a: eqtype -> #b: eqtype -> f: (a -> b) ->  s: seq a -> 
  Tot (r: seq b{Seq.length s = Seq.length r /\
    (forall (i: nat {i < Seq.length s}). index r i = f (index s i))})
  (decreases (Seq.length s))



let contains (#a:Type) (f: (a -> bool)) (s:seq a)  : Tot Type0 =
  exists (k:nat{k < Seq.length s}). f (Seq.index s k)
