module PKCS11.Spec.Lemmas


open FStar.UInt32
open FStar.Seq
open FStar.Option

open FStar.Seq.Base
open FStar.Seq.Properties


val for_all2: #a: eqtype -> #b: eqtype -> f: (x: a -> y:b -> bool) -> s: seq a -> s1: seq b{Seq.length	s = Seq.length s1} -> 
	Tot bool (decreases (Seq.length s))

let rec for_all2 #a #b f s s1 = 
	if length s = 0 then true else
	let element = f (head s) (head s1) in 
	if element = false then false else
	for_all2 #a #b f (tail s) (tail s1)

val _for_all2_2: #a: eqtype -> #b: eqtype -> f: (x: a -> y: b -> bool) -> s: seq a -> s1: seq b {Seq.length s = Seq.length s1} -> 
	counter: nat {counter < Seq.length s \/ Seq.length s = 0} -> Tot bool (decreases (Seq.length s - counter))

let rec _for_all2_2 #a #b f s s1 counter = 
	if length s = 0 then true else 
	let element1 = Seq.index s counter in 
	let element2 = Seq.index s1 counter in 
	let r = f element1 element2 in 
	if r = false then false 
	else if (counter+1 < Seq.length s) then 
		_for_all2_2 #a #b f s s1 (counter+1) 
	else true	


val for_all2_2: #a: eqtype -> #b: eqtype -> f: (x: a -> y: b -> bool) -> s: seq a -> s1: seq b{Seq.length s = Seq.length s1} -> Tot bool

let for_all2_2 #a #b f s s1 = 
	_for_all2_2 #a #b f s s1 0


assume val map: #a: eqtype -> #b: eqtype -> 
	f: (a -> b) ->  s: seq a -> Tot (r: seq b{Seq.length s = Seq.length r /\
		(forall (i: nat {i < Seq.length s}). index r i = f (index s i))})
	(decreases (Seq.length s))

val lemma_find: #a: eqtype -> s: seq a -> e: seq a ->f: (a -> bool) ->  Lemma
	(ensures (find_l f (append s e) = find_l f  (append e s)))


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


assume val lemma_append_count: #a:eqtype -> lo:seq a -> hi:seq a ->f: (a -> Tot bool) -> Lemma
  (requires True)
  (ensures (count f (append lo hi) = (count f lo + count f hi)))
  (decreases (length lo))


(*  Just takes too much time *)
(*) 
let rec lemma_append_count #a lo hi f=
  if length lo = 0
  then cut (equal (append lo hi) hi)
  else (cut (equal (cons (head lo) (append (tail lo) hi))
                (append lo hi));
        lemma_append_count (tail lo) hi f;
        let tl_l_h = append (tail lo) hi in
        let lh = cons (head lo) tl_l_h in
        cut (equal (tail lh) tl_l_h))
*)

val seq_remove_lemma: #a: eqtype -> s: seq a -> f : (a -> bool) -> Lemma
	(requires (forall (i: nat {i < Seq.length s}). not (f(Seq.index s i))))
	(ensures (None? (find_l f s)))
	(decreases (Seq.length s))

let rec seq_remove_lemma #a s f = 
	if length  s = 0 then ()
	else seq_remove_lemma #a (tail s) f


assume val seq_remove: #a: eqtype -> s: seq a -> f: (a -> bool) -> Tot 
	(r: seq a {
		(forall (i: nat{i < Seq.length r}). not (f(Seq.index r i))) /\ None? (find_l f r) /\
		(forall x. if Seq.count x s = 0 then Seq.count x r = 0 else if Seq.count x s > 0 && f (x) then Seq.count x r = 0 else Seq.count x s = Seq.count x r)
		}
	) 
	(decreases (Seq.length s))



(* let rec seq_remove #a s f = 
	if length s = 0 then Seq.createEmpty else
	if f (head s) = false then 
		let s' = tail s in 
		let r' = seq_remove #a s' f in 
		let r = Seq.append (Seq.create 1 (head s)) r' in 
			assert(Seq.count (head s) s' = Seq.count (head s) r');

			lemma_append_count_aux (head s) (Seq.create 1 (head s)) r';
			assert(Seq.count (head s) r = Seq.count (head s) r' + 1);

			lemma_append_count_aux (head s) (Seq.create 1 (head s)) (tail s);
			assert(Seq.count (head s) s = Seq.count (head s) (tail s) + 1);
		seq_remove_lemma r f; 

		r
	else 
		let r = seq_remove #a (tail s) f in 
		seq_remove_lemma r f;
		admit();
		r *)

assume val seq_getIndex: #a: eqtype -> s: seq a -> el: a {count el s > 0} -> Tot (i: nat {Seq.index s i = el})

