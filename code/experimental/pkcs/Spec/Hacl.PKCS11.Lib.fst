module Hacl.PKCS11.Lib

open FStar.Seq



let for_all
  (#a: Type)
  (f: (a -> Tot bool))
  (l: seq a)
: Pure bool
  (requires True)
  (ensures (fun b -> (b == true <==> (forall (i: nat). i < Seq.length l /\ f (index l i) == true))))
= None? (seq_find (fun i -> not (f i)) l)


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



let contains (#a:Type) (f: (a -> bool)) (s:seq a) : Tot Type0 =
  exists (k:nat). k < Seq.length s /\  f (Seq.index s k) 


val containsLemma: #a: eqtype -> s: seq a {length s > 0} -> Lemma 
  (
    forall (i: nat). i < Seq.length s /\ contains (fun x -> x = (index s i)) s
  )

let rec containsLemma #a s = 
  let open FStar.Classical in 

  let x: n: nat {n > 10} = 11 in 
  give_witness x; 

  admit();
  assert(forall (k: nat {k < length s}).  (fun x -> x = (index s k)) (index s k));
  assume(exists (k: nat). k < length s /\ (fun x -> x = (index s k)) (index s k));
  admit()
