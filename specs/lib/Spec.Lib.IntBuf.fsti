module Spec.Lib.IntBuf

open FStar.HyperStack
open FStar.HyperStack.ST
open Spec.Lib.IntTypes

module LSeq = Spec.Lib.IntSeq


val lbuffer: a:Type0 -> len:size_t -> Type0
val sub: #a:Type0 -> #len:size_t -> b:lbuffer a len -> start:size_t -> n:size_t{start + n <= len} -> Tot (lbuffer a n)
let slice #a #len (b:lbuffer a len) (start:size_t) (fin:size_t{fin <= len /\ start <= fin}) = sub #a #len b start (fin - start)
noeq type bufitem = | BufItem: a:Type0 -> len:size_t -> buf:lbuffer a len -> bufitem

val disjoint: #a1:Type0 -> #a2:Type0 -> #len1:size_t -> #len2:size_t -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> GTot Type
val live: #a:Type0 -> #len:size_t ->  mem -> lbuffer a len -> GTot Type
val preserves_live: mem -> mem -> GTot Type
val as_lseq: #a:Type0 -> #len:size_t -> lbuffer a len -> mem -> GTot (LSeq.lseq a len)

val live_sub_lemma: #a:Type0 -> #len:size_t -> h:mem -> b:lbuffer a len -> start:size_t -> n:size_t{start + n <= len} -> Lemma
			 (requires (live h b))
			 (ensures (live h (sub b start n)))
			 [SMTPat (live h (sub b start n))]

val live_super_lemma: #a:Type0 -> #len:size_t -> h:mem -> b:lbuffer a len -> start:size_t -> n:size_t{start + n <= len} -> Lemma
			 (requires (live h (sub b start n)))
			 (ensures (live h b))
			 [SMTPat (live h (sub b start n))]

val disjoint_self_lemma: #a:Type0 -> #len:size_t -> b:lbuffer a len -> Lemma
			 (requires (True))
			 (ensures (~ (disjoint b b)))
			 [SMTPat (disjoint b b)]

val disjoint_sub_lemma1: #a1:Type0 -> #a2:Type0 -> #len1:size_t -> #len2:size_t -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> start1:size_t -> n1:size_t{start1 + n1 <= len1} -> Lemma
			 (requires (disjoint b1 b2))
			 (ensures (disjoint (sub b1 start1 n1) b2 /\ disjoint b2 (sub b1 start1 n1)))
			 [SMTPat (disjoint (sub b1 start1 n1) b2 \/ disjoint b2 (sub b1 start1 n1))]

val disjoint_sub_lemma2: #a:Type0 -> #len:size_t -> b:lbuffer a len -> start1:size_t -> n1:size_t{start1 + n1 <= len} -> start2:size_t -> n2:size_t{start2 + n2 <= len} -> Lemma
			 (requires (start1 + n1 <= start2 \/ start2 + n2 <= start1))
			 (ensures (disjoint (sub b start1 n1) (sub b start2 n2)))
			 [SMTPat (disjoint (sub b start1 n1) (sub b start2 n2))]

val as_lseq_sub_lemma: #a:Type0 -> #len:size_t -> h:mem -> b:lbuffer a len -> start:size_t -> n:size_t{start + n <= len} -> Lemma
			 (requires (live h b))
			 (ensures (as_lseq (sub b start n) h == LSeq.sub (as_lseq b h) start n))
			 [SMTPat (as_lseq (sub b start n) h)]
			 
			 
val preserves_live_lemma: #a:Type0 -> #len:size_t -> b:lbuffer a len -> h0:mem -> h1:mem -> Lemma
			 (requires (preserves_live h0 h1 /\ live h0 b))
			 (ensures  (live h1 b))
			 [SMTPat (preserves_live h0 h1 /\ live h0 b)]


//val creates1: #a:Type0 -> #len:size_t -> b:lbuffer a len -> h0:mem -> h1:mem -> GTot Type 
let creates1 (#a:Type0) (#len:size_t) (b:lbuffer a len) (h0:mem) (h1:mem) : GTot Type = 
 (live h1 b /\
  (forall (a':Type0) (len':size_t) (b':lbuffer a' len'). {:pattern (live h0 b')} live h0 b' ==> (live h1 b' /\ disjoint b b'  /\ disjoint b' b)))
  
val creates1_lemma:  #a1:Type0 -> #a2:Type0 -> #len1:size_t -> #len2:size_t -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> h0:mem -> h1:mem -> Lemma
			 (requires (live h0 b1 /\ creates1 b2 h0 h1))
			 (ensures  (live h1 b1 /\ disjoint b1 b2 /\ disjoint b2 b1))
			 [SMTPat (creates1 b2 h0 h1 /\ live h0 b1)]


let creates2 #a1 #a2 #len1 #len2 (b1:lbuffer a1 len1) (b2:lbuffer a2 len2) h0 h1 = 
  creates1 #a1 #len1 b1 h0 h1 /\
  creates1 #a2 #len2 b2 h0 h1 

let creates3 #a1 #a2 #a3  #len1 #len2  #len3 (b1:lbuffer a1 len1) (b2:lbuffer a2 len2) (b3:lbuffer a3 len3) h0 h1 = 
  creates1 #a1 #len1 b1 h0 h1 /\
  creates1 #a2 #len2 b2 h0 h1 /\
  creates1 #a3 #len3 b3 h0 h1 

let rec creates (l:list bufitem) (h0:mem) (h1:mem) : GTot Type = 
  match l with
  | [] -> True
  | b::t -> creates1 b.buf h0 h1 /\ creates t h0 h1
  
//val modifies1: #a:Type0 -> #len:size_t ->  lbuffer a len -> mem -> mem -> GTot Type
let modifies1 (#a:Type0) (#len:size_t) (b:lbuffer a len) (h0:mem) (h1:mem) : GTot Type =
  (live h1 b /\
  (forall (a':Type0) (len':size_t) (b':lbuffer a' len'). {:pattern (live h0 b' /\ disjoint b' b)} 
		(live h0 b' /\ disjoint b' b) ==> (live h1 b'  /\ as_lseq b' h1 == as_lseq b' h0)))

//val modifies2: #a1:Type0 -> #a2:Type0 -> #len1:size_t -> #len2:size_t -> lbuffer a1 len1 -> lbuffer a2 len2 -> mem -> mem -> GTot Type
let modifies2 (#a1:Type0) (#a2:Type0) (#len1:size_t) (#len2:size_t) (b1:lbuffer a1 len1) (b2:lbuffer a2 len2) (h0:mem) (h1:mem) : GTot Type =
  (live h1 b1 /\ live h1 b2 /\
  (forall (a':Type0) (len':size_t) (b':lbuffer a' len'). {:pattern (live h0 b' /\ disjoint b' b1 /\ disjoint b' b2)} 
		(live h0 b' /\ disjoint b' b1 /\ disjoint b' b2) ==> (live h1 b'  /\ as_lseq b' h1 == as_lseq b' h0)))

//val modifies3: #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len1:size_t -> #len2:size_t -> #len3:size_t -> lbuffer a1 len1 -> lbuffer a2 len2 -> lbuffer a3 len3 -> mem -> mem -> GTot Type
let modifies3 (#a1:Type0) (#a2:Type0) (#a3:Type0) (#len1:size_t) (#len2:size_t)  (#len3:size_t) (b1:lbuffer a1 len1) (b2:lbuffer a2 len2) (b3:lbuffer a3 len3) (h0:mem) (h1:mem) : GTot Type =
  (live h1 b1 /\ live h1 b2 /\ live h1 b3 /\ 
  (forall (a':Type0) (len':size_t) (b':lbuffer a' len'). {:pattern (live h0 b' /\ disjoint b' b1 /\ disjoint b' b2 /\ disjoint b' b3)} 
		(live h0 b' /\ disjoint b' b1 /\ disjoint b' b2 /\ disjoint b' b3) ==> (live h1 b'  /\ as_lseq b' h1 == as_lseq b' h0)))

let rec live_list (l:list bufitem) (h1:mem) : GTot Type = 
  match l with
  | [] -> True
  | h::t -> (live h1 h.buf /\ live_list t h1)

let rec disjoint_list #a #len (b:lbuffer a len) (l:list bufitem) : GTot Type = 
  match l with
  | [] -> True
  | h::t -> (disjoint b h.buf /\ disjoint_list b t)

//val modifies: list bufitem -> mem -> mem -> GTot Type
let modifies (l:list bufitem) (h0:mem) (h1:mem) : GTot Type = 
    match l with
    | [] -> h0 == h1
    | [x] -> modifies1 x.buf h0 h1
    | [x1;x2] -> modifies2 x1.buf x2.buf h0 h1
    | [x1;x2;x3] -> modifies3 x1.buf x2.buf x3.buf h0 h1
    | l -> live_list l h1 /\ 
	  (forall (a':Type0) (len':size_t) (b':lbuffer a' len'). {:pattern (live h0 b' /\ disjoint_list b' l)} 
	     (live h0 b' /\ disjoint_list b' l) ==> (live h1 b' /\ as_lseq b' h1 == as_lseq b' h0))

    
val modifies1_lemma:  #a1:Type0 -> #a2:Type0 -> #len1:size_t -> #len2:size_t -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> h0:mem -> h1:mem -> Lemma
			 (requires (disjoint b1 b2 /\ live h0 b1 /\ modifies1 b2 h0 h1))
			 (ensures  (live h1 b1 /\ as_lseq b1 h1 == as_lseq b1 h0))
			 [SMTPat (disjoint b1 b2 /\ modifies1 b2 h0 h1)]


val modifies2_lemma:  #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len1:size_t -> #len2:size_t -> #len3:size_t -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> h0:mem -> h1:mem -> Lemma
			 (requires (disjoint b1 b2 /\ disjoint b1 b3 /\ live h0 b1 /\ modifies2 b2 b3 h0 h1))
			 (ensures  (live h1 b1 /\ as_lseq b1 h1 == as_lseq b1 h0))
			 [SMTPat (disjoint b1 b2 /\ modifies2 b2 b3 h0 h1)]


val modifies3_lemma:  #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #a4:Type0-> #len1:size_t -> #len2:size_t -> #len3:size_t -> #len4:size_t -> 
		      b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> b4:lbuffer a4 len4 -> h0:mem -> h1:mem -> Lemma
			 (requires (disjoint b1 b2 /\ disjoint b1 b3 /\ disjoint b1 b4 /\ live h0 b1 /\ modifies3 b2 b3 b4 h0 h1))
			 (ensures  (live h1 b1 /\ as_lseq b1 h1 == as_lseq b1 h0))
			 [SMTPat (disjoint b1 b2 /\ modifies3 b2 b3 b4 h0 h1)]



val create: #a:Type0 -> len:size_t -> init:a -> Stack (lbuffer a len)
		      (requires (fun h0 -> True))
		      (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ creates1 r h0 h1 /\ modifies1 r h0 h1 /\ as_lseq #a #len r h1 == LSeq.create #a len init))
		      
val createL: #a:Type0 -> init:list a{List.Tot.length init <= max_size_t} -> Stack (lbuffer a (List.Tot.length init))
		      (requires (fun h0 -> True))
		      (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ creates1 r h0 h1 /\ modifies1 r h0 h1 /\ as_lseq #a #(List.Tot.length init) r h1 == LSeq.createL #a init))

val index: #a:Type0 -> #len:size_t -> b:lbuffer a len -> i:size_t{i < len} -> Stack a 
		      (requires (fun h0 -> live h0 b))
		      (ensures (fun h0 r h1 -> h0 == h1 /\ r == LSeq.index #a #len (as_lseq #a #len b h0) i)) 

val upd: #a:Type0 -> #len:size_t -> b:lbuffer a len -> i:size_t{i < len} -> v:a -> Stack unit 
		      (requires (fun h0 -> live h0 b /\ len > 0))
		      (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ modifies1 b h0 h1 /\ as_lseq #a #len b h1 == LSeq.upd #a #len (as_lseq #a #len b h0) i v))

val map: #a:Type -> #len:size_t -> f:(a -> Tot a) -> b:lbuffer a len -> Stack unit 
		      (requires (fun h0 -> live h0 b))
		      (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 b h0 h1 /\ as_lseq #a #len b h1 == LSeq.map #a #a #len f (as_lseq #a #len b h0)))

val map2: #a1:Type -> #a2:Type -> #len:size_t -> f:(a1 -> a2 -> Tot a1) -> b1:lbuffer a1 len -> b2:lbuffer a2 len -> Stack unit 
		      (requires (fun h0 -> live h0 b1 /\ live h0 b2))
		      (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 b1 h0 h1 /\ as_lseq #a1 #len b1 h1 == LSeq.map2 #a1 #a2 #a1 #len f (as_lseq #a1 #len b1 h0) (as_lseq #a2 #len b2 h0)))

val repeat: #a:Type -> #b:Type -> #lift:(mem -> b -> GTot (option a)) -> 
	    n:size_t -> spec:(a -> Tot a) -> 
	    impl:(x:b -> Stack unit (requires (fun h0 -> Some? (lift h0 x))) (ensures (fun h0 _ h1 -> Some? (lift h0 x) /\ Some? (lift h1 x) /\ Some?.v (lift h1 x) == spec (Some?.v (lift h0 x))))) ->
	    input:b ->
	    Stack unit
	    (requires (fun h0 -> Some? (lift h0 input)))
	    (ensures (fun h0 _ h1 -> Some? (lift h0 input) /\ Some? (lift h1 input) /\
				  Some?.v (lift h1 input) ==  LSeq.repeat n spec (Some?.v (lift h0 input))))


val repeat_range: #a:Type -> #b:Type -> #lift:(mem -> b -> GTot (option a)) -> 
	    start:size_t -> fin:size_t{start <= fin} -> spec:(i:size_t{start <= i /\ i < fin} -> a -> Tot a) -> 
	    impl:(i:size_t{start <= i /\ i < fin} -> x:b -> Stack unit 
				   (requires (fun h0 -> Some? (lift h0 x))) 
				   (ensures (fun h0 _ h1 -> Some? (lift h0 x) /\ Some? (lift h1 x) /\ 
							 Some?.v (lift h1 x) == spec i (Some?.v (lift h0 x))))) ->
	    input:b ->
	    Stack unit
	    (requires (fun h0 -> Some? (lift h0 input)))
	    (ensures (fun h0 _ h1 -> Some? (lift h0 input) /\ Some? (lift h1 input) /\
				  Some?.v (lift h1 input) ==  LSeq.repeat_range start fin spec (Some?.v (lift h0 input))))

val repeati: #a:Type -> #b:Type -> #lift:(mem -> b -> GTot (option a)) -> 
	    n:size_t -> spec:(i:size_t{i < n} -> a -> Tot a) -> 
	    impl:(i:size_t{i < n} -> x:b -> Stack unit 
				   (requires (fun h0 -> Some? (lift h0 x))) 
				   (ensures (fun h0 _ h1 -> Some? (lift h0 x) /\ Some? (lift h1 x) /\ 
							 Some?.v (lift h1 x) == spec i (Some?.v (lift h0 x))))) ->
	    input:b ->
	    Stack unit
	    (requires (fun h0 -> Some? (lift h0 input)))
	    (ensures (fun h0 _ h1 -> Some? (lift h0 input) /\ Some? (lift h1 input) /\
				  Some?.v (lift h1 input) ==  LSeq.repeati n spec (Some?.v (lift h0 input))))

val iter: #a:Type -> #len:size_t -> n:size_t -> spec:(LSeq.lseq a len -> Tot (LSeq.lseq a len)) -> 
         impl:(x:lbuffer a len -> Stack unit 
			(requires (fun h0 -> live h0 x))
			(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ 
				              modifies1 x h0 h1 /\
					      as_lseq #a #len x h1 == spec (as_lseq #a #len x h0)))) ->
	    input:lbuffer a len ->
	    Stack unit
	    (requires (fun h0 -> live h0 input))
	    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 input h1 h1 /\
				  as_lseq #a #len input h1 ==  LSeq.repeat n spec (as_lseq #a #len input h0)))

val iteri: #a:Type -> #len:size_t -> n:size_t -> spec:(i:size_t{i < n}  -> LSeq.lseq a len -> Tot (LSeq.lseq a len)) -> 
         impl:(i:size_t{i < n}  -> x:lbuffer a len -> Stack unit 
			(requires (fun h0 -> live h0 x))
			(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ 
				              modifies1 x h0 h1 /\
					      as_lseq #a #len x h1 == spec i (as_lseq #a #len x h0)))) ->
	    input:lbuffer a len ->
	    Stack unit
	    (requires (fun h0 -> live h0 input))
	    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 input h1 h1 /\
				  as_lseq #a #len input h1 ==  LSeq.repeati n spec (as_lseq #a #len input h0)))

val iter_range: #a:Type -> #len:size_t -> start:size_t -> fin:size_t{start <= fin} ->
         spec:(i:size_t{start <= i /\ i < fin}  -> LSeq.lseq a len -> Tot (LSeq.lseq a len)) -> 
         impl:(i:size_t{start <= i /\ i < fin}  -> x:lbuffer a len -> Stack unit 
			(requires (fun h0 -> live h0 x))
			(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ 
				              modifies1 x h0 h1 /\
					      as_lseq #a #len x h1 == spec i (as_lseq #a #len x h0)))) ->
	    input:lbuffer a len ->
	    Stack unit
	    (requires (fun h0 -> live h0 input))
	    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 input h1 h1 /\
				  as_lseq #a #len input h1 ==  LSeq.repeat_range start fin spec (as_lseq #a #len input h0)))


