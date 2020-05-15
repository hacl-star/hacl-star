module Hacl.PKCS11.Lib

open FStar.Seq


val count : #a:eqtype -> f: (a -> Tot bool) -> s:seq a -> Tot nat (decreases (length s))

let rec count #a f s =
  if length s = 0 then 0
  else if  f (head s) = true
  then 1 + count f (tail s)
  else count f (tail s)

val lemmaNoneIsCount0: #a: eqtype -> f: (a -> Tot bool) -> s: seq a -> 
  Lemma 
    (requires (None? (find_l f s)))
    (ensures (count f s = 0))
    (decreases (length s))

let rec lemmaNoneIsCount0 #a f s = 
  if length s = 0 then () else 
  lemmaNoneIsCount0 f (tail s)


val countMore0IsSome: #a: eqtype -> s: seq a -> f: (a -> bool) -> Lemma
  (requires (count f s > 0))
  (ensures (Some? (find_l f s))) 
  (decreases (Seq.length s))

let rec countMore0IsSome #a s f = 
  if length s = 0 then ()
  else if f (head s) then () else
  countMore0IsSome #a (tail s) f	


let for_all
  (#a: Type)
  (f: (a -> Tot bool))
  (l: seq a)
: Pure bool
  (requires True)
  (ensures (fun b -> (b == true <==> (forall (i: nat). i < Seq.length l ==> f (index l i) == true))))
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
    (forall (i: nat). i < Seq.length s ==> index r i = f (index s i))})
  (decreases (Seq.length s))
 


let contains (#a:Type) (f: (a -> bool)) (s:seq a) : Tot Type0 =
  exists (k:nat). k < Seq.length s /\  f (Seq.index s k) 


#set-options "--z3rlimit 300"


val containsLemma: #a: eqtype -> s: seq a {length s > 0} -> Lemma 
  (
    forall (i: nat). i < Seq.length s ==> contains (fun x -> x = (index s i)) s
  )

let rec containsLemma #a s = admit()


val takeOne: #a: eqtype -> 
  f: (a -> Tot bool) ->
  s: seq a ->   
  counter: nat {counter <= length s}-> 
  seqToPut: seq a 
    {
      (forall (i: nat). i < length seqToPut ==> f (index seqToPut i)) /\
      (forall (i: nat). i < length seqToPut ==> (exists (n: nat {n < length s}). index s n == index seqToPut i))
    } -> 
  Tot (r: seq a {
    (
      forall (i: nat). i < Seq.length r ==> f (index r i)) /\
      (forall (i: nat). i < length r ==> (exists (n: nat {n < length s}). index s n == index r i))
  })
  (decreases (length s - counter))
  

let rec takeOne #a f s counter seqToPut = 
  let _takeOne f s counter seqToPut = 
      let element = index s counter in 
      if f element then 
	snoc seqToPut element
      else 
	seqToPut in 
  if counter = length s then seqToPut 
  else
    begin
    let seqToPutForCurrent = _takeOne f s counter seqToPut in 
    takeOne f s (counter + 1) seqToPutForCurrent
    end


val takeAll: #a: eqtype -> f: (a -> Tot bool) -> s: seq a ->
  Tot (r: seq a {
    (
      forall (i: nat). i < length r ==> f (index r i)) /\
      (forall (i: nat). i < length r ==> (exists (n: nat {n < length s}). index s n == index r i)) /\
      count f s == count f r}
    )

let takeAll #a f s = 
  admit();
  takeOne f s 0 (Seq.empty)
  
