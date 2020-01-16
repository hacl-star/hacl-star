module PKCS11.Spec.Lemmas


open FStar.UInt32
open FStar.Seq
open FStar.Option

open FStar.Seq.Base
open FStar.Seq.Properties

#set-options "--z3rlimit 300"

assume val find_append_some_s2: #a:Type -> s1:seq a -> s2:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (Some? (find_l f s2)))
  (ensures (find_l f (append s1 s2) == find_l f s2))
  (decreases (length s1))

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


val map: #a: eqtype -> #b: eqtype -> 
	f: (a -> b) ->  s: seq a -> Tot (r: seq b{Seq.length s = Seq.length r /\
		(forall (i: nat {i < Seq.length s}). index r i = f (index s i))})
	(decreases (Seq.length s))

let rec map #a #b f s = 
	if length s = 0 then Seq.createEmpty 
	else
		let h = Seq.create 1 (f (head s)) in 
		let tail = map f (tail s) in 
		Seq.append h tail

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


val lemma_append_count2: #a:eqtype -> lo:seq a -> hi:seq a ->f: (a -> Tot bool) -> Lemma
  (requires True)
  (ensures (count f (append lo hi) = (count f lo + count f hi)))
  (decreases (length lo))


let rec lemma_append_count2 #a lo hi f=
  if length lo = 0
  then cut (equal (append lo hi) hi)
  else (cut (equal (cons (head lo) (append (tail lo) hi))
                (append lo hi));
        lemma_append_count2 (tail lo) hi f;
        let tl_l_h = append (tail lo) hi in
        let lh = cons (head lo) tl_l_h in
        cut (equal (tail lh) tl_l_h))

val lemma_append_count_aux2: #a:eqtype -> f:( a -> bool) -> lo:seq a -> hi:seq a -> Lemma
  (requires True)
  (ensures (count f (append lo hi) = (count f lo + count f hi)))

let lemma_append_count_aux2 #a f lo hi = lemma_append_count2 lo hi f 


assume val seq_getIndex2: #a: eqtype -> f: (a -> Tot bool) -> s: seq a{count f s > 0} -> Tot (i: nat {i < Seq.length s /\ f (Seq.index s i) == true})


assume val lemma_getIndex2: #a: eqtype -> f: (a -> bool) ->   s: seq a -> el: a {f el} -> Lemma
	(requires (count f s = 0))
	(ensures (let s1 = Seq.create 1 el in 
		lemma_append_count_aux2 f s s1;
		seq_getIndex2 f (Seq.append s s1) = Seq.length s))

val seq_remove: #a: eqtype -> s: seq a -> f: (a -> bool) -> Tot 
	(r: seq a {count f r = 0 }) 
	(decreases (Seq.length s))


let rec seq_remove #a s f = 
	if length s = 0 then Seq.createEmpty 
	else if f (head s) = false then 
		let tail_part = seq_remove (tail s) f in 
		let head_part = Seq.create 1 (head s) in 
		lemma_append_count_aux2 f head_part tail_part;	
		Seq.append head_part tail_part
	else 
		begin 
			seq_remove (tail s) f
		end


val seq_remove_lemma_count_of_deleted: #a: eqtype -> s: seq a -> f: (a -> bool) -> Lemma
	(ensures (
		let toDelete = count f s in 
		let lengthBefore = Seq.length s in 
		let removed = seq_remove s f in 
		Seq.length removed = Seq.length s - toDelete
	))
	(decreases (Seq.length s))

let rec seq_remove_lemma_count_of_deleted #a s f = 
	if Seq.length s = 0 then () 
	else
		seq_remove_lemma_count_of_deleted (tail s) f


val seq_remove_unchanged: #a: eqtype -> s: seq a -> f: (a -> bool) -> Lemma
	(requires (count f s = 1))
	(ensures 
		(	
			let r = seq_remove s f in 
			count f s = 1  /\ 
			Seq.length r = Seq.length s -1 /\
			(
				let index_to_delete = seq_getIndex2 #a f s in 
				let a, hb = Seq.split s index_to_delete in 
				let _, b = Seq.split hb 1 in 
				let a_, b_ = Seq.split r index_to_delete in 
				a == a_ /\ b == b_
			)
		)
	)
	(decreases (Seq.length s))

let rec seq_remove_unchanged #a s f = 
	if Seq.length s = 0 then () else
	admit()

(* changed from 0 *)
assume val seq_getIndex: #a: eqtype -> s: seq a -> el: a{Seq.count el s  =  1}  -> Tot (i: nat {i< Seq.length s /\ Seq.index s i == el})

assume val lemma_getIndex: #a: eqtype ->el: a ->  s: seq a -> Lemma
	(requires (Seq.count el s = 0))
	(ensures (let s1 = Seq.create 1 el in 
		let newS = Seq.append s s1 in 
		lemma_append_count_aux el s s1;
		seq_getIndex newS el = Seq.length s))


val countMore0IsSome: #a: eqtype -> s: seq a -> f: (a -> bool) -> Lemma
	(requires (count f s > 0))
	(ensures (Some? (find_l f s))) 
	(decreases (Seq.length s))

let rec countMore0IsSome #a s f = 
	if length s = 0 then ()
	else if f(head s) then () else
	countMore0IsSome #a (tail s) f	


assume val countFCount: #a: eqtype -> f: (a -> Tot bool) -> s: seq a -> el:a {f el == true} -> Lemma
	(requires (count f s = 0))
	(ensures (Seq.count el s = 0))

	
assume val lemma_append: #a: eqtype -> s: seq a -> s1: seq a -> 
	Lemma (ensures (let a, b = Seq.split (Seq.append s s1) (Seq.length s) in a==s))
	(decreases (Seq.length s))

