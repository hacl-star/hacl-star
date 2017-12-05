module Spec.Lib.IntBuf

open FStar.HyperStack
open FStar.HyperStack.ST
open Spec.Lib.IntTypes

module LSeq = Spec.Lib.IntSeq


val lbuffer: a:Type0 -> len:size_t -> Type0
val sub: #a:Type0 -> #len:size_t -> b:lbuffer a len -> start:size_t -> n:size_t{start + n <= len} -> Tot (lbuffer a n)
let slice #a #len (b:lbuffer a len) (start:size_t) (fin:size_t{fin <= len /\ start <= fin}) = sub #a #len b start (fin - start)
noeq type bufitem = | BufItem: #a:Type0 -> #len:size_t -> buf:lbuffer a len -> bufitem

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
			 [SMTPat (disjoint (sub b1 start1 n1) b2);
			  SMTPat (disjoint b2 (sub b1 start1 n1))]

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
			 [SMTPat (preserves_live h0 h1);
			  SMTPat (live h0 b)]


//val creates1: #a:Type0 -> #len:size_t -> b:lbuffer a len -> h0:mem -> h1:mem -> GTot Type 
let creates1 (#a:Type0) (#len:size_t) (b:lbuffer a len) (h0:mem) (h1:mem) : GTot Type = 
 (live h1 b /\
  (forall (a':Type0) (len':size_t) (b':lbuffer a' len'). {:pattern (live h0 b')} live h0 b' ==> (live h1 b' /\ disjoint b b'  /\ disjoint b' b)))
  
val creates1_lemma:  #a1:Type0 -> #a2:Type0 -> #len1:size_t -> #len2:size_t -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> h0:mem -> h1:mem -> Lemma
			 (requires (live h0 b1 /\ creates1 b2 h0 h1))
			 (ensures  (live h1 b1 /\ disjoint b1 b2 /\ disjoint b2 b1))
			 [SMTPat (creates1 b2 h0 h1);
			  SMTPat (live h0 b1)]

val creates1_preserves:  #a1:Type0 -> #len1:size_t -> b:lbuffer a1 len1 -> h0:mem -> h1:mem -> h2:mem -> Lemma
			 (requires (preserves_live h0 h1 /\ creates1 b h1 h2))
			 (ensures  (creates1 b h0 h1))
			 [SMTPat (creates1 b h1 h2);
			  SMTPat (preserves_live h0 h1)]

val creates1_preserves':  #a1:Type0 -> #len1:size_t -> b:lbuffer a1 len1 -> h0:mem -> h1:mem -> h2:mem -> Lemma
			 (requires (creates1 b h0 h1 /\ preserves_live h1 h2))
			 (ensures  (creates1 b h0 h2))
			 [SMTPat (creates1 b h0 h1);
			  SMTPat (preserves_live h1 h2)]

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
  
val modifies1: #a:Type0 -> #len:size_t ->  lbuffer a len -> mem -> mem -> GTot Type
val modifies2: #a1:Type0 -> #a2:Type0 -> #len1:size_t -> #len2:size_t -> lbuffer a1 len1 -> lbuffer a2 len2 -> mem -> mem -> GTot Type
val modifies3: #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len1:size_t -> #len2:size_t -> #len3:size_t -> lbuffer a1 len1 -> lbuffer a2 len2 -> lbuffer a3 len3 -> mem -> mem -> GTot Type
val modifies: list bufitem -> mem -> mem -> GTot Type
val live_list: mem -> list bufitem -> GTot Type
val disjoint_list: #a:Type0 -> #len:size_t -> b:lbuffer a len -> list bufitem  -> GTot Type

val live_list_lemma1: #a:Type0 -> #len:size_t -> b:lbuffer a len -> h:mem -> Lemma
			(requires (True))
			(ensures (live_list h [BufItem b] == live h b))
			[SMTPat (live_list h [BufItem b])]

val live_list_lemma2: #a1:Type0 -> #a2:Type0 -> #len1:size_t -> #len2:size_t -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> h:mem -> Lemma
			(requires (True))
			(ensures (live_list h [BufItem b1; BufItem b2] == (live h b1 /\ live h b2)))
			[SMTPat (live_list h [BufItem b1; BufItem b2])]

val live_list_lemma3: #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len1:size_t -> #len2:size_t -> #len3:size_t -> 
			b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> h:mem -> Lemma
			(requires (True))
			(ensures (live_list h [BufItem b1; BufItem b2; BufItem b3] == (live h b1 /\ live h b2 /\ live h b3)))
			[SMTPat (live_list h [BufItem b1; BufItem b2; BufItem b3])]


val disjoint_list_lemma1: #a:Type0 -> #a1:Type0 -> #len:size_t -> #len1:size_t -> b0:lbuffer a len -> b:lbuffer a len -> Lemma
			(requires (True))
			(ensures (disjoint_list b0 [BufItem b] == (disjoint b0 b /\ disjoint b b0) ))
			[SMTPat (disjoint_list b0 [BufItem b])]

val disjoint_list_lemma2: #a0:Type0 -> #a1:Type0 -> #a2:Type0 -> #len0:size_t -> #len1:size_t -> #len2:size_t -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 ->  Lemma
			(requires (True))
			(ensures (disjoint_list b0 [BufItem b1; BufItem b2] == (disjoint b0 b1 /\ disjoint b0 b2 /\ disjoint b1 b0 /\ disjoint b2 b0)))
			[SMTPat (disjoint_list b0 [BufItem b1; BufItem b2])]

val disjoint_list_lemma3: #a0:Type0 -> #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len0:size_t -> #len1:size_t -> #len2:size_t -> #len3:size_t -> 
			b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> Lemma
			(requires (True))
			(ensures (disjoint_list b0 [BufItem b1; BufItem b2; BufItem b3] == (disjoint b0 b1 /\ disjoint b0 b2 /\ disjoint b0 b3 /\ disjoint b1 b0 /\ disjoint b2 b0 /\ disjoint b3 b0)))
			[SMTPat (disjoint_list b0 [BufItem b1; BufItem b2; BufItem b3])]

val modifies_modifies_1: #a:Type0 -> #len:size_t -> b:lbuffer a len -> h0:mem -> h1:mem -> Lemma
			(requires (True))
			(ensures (modifies [BufItem b] h0 h1 == modifies1 b h0 h1))
			[SMTPat (modifies [BufItem b] h0 h1)]

val list_cons1_lemma: #a:Type0 -> x:a -> y:a -> Lemma
			 (requires True)
			 (ensures ([x;y] == x::[y]))
			 [SMTPat (x::[y])]
val list_cons2_lemma: #a:Type0 -> x:a -> y:a -> z:a -> Lemma
			 (requires True)
			 (ensures ([x;y;z] == x::[y;z]))
			 [SMTPat (x::[y;z])]
			 
val modifies_modifies_2: #a1:Type0 -> #a2:Type0 -> #len1:size_t -> #len2:size_t -> 
			b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> h0:mem -> h1:mem -> Lemma
			(requires (True))
			(ensures (modifies [BufItem b1; BufItem b2] h0 h1 == modifies2 b1 b2 h0 h1))
			[SMTPat (modifies [BufItem b1; BufItem b2] h0 h1)]

val modifies_modifies_3: #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len1:size_t -> #len2:size_t -> #len3:size_t -> 
			b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> 
			h0:mem -> h1:mem -> Lemma
			(requires True) 
			(ensures (modifies [BufItem b1; BufItem b2; BufItem b3] h0 h1 == modifies3 b1 b2 b3 h0 h1))
			[SMTPat (modifies [BufItem b1; BufItem b2; BufItem b3] h0 h1)]

val preserves_live_refl: h0:mem -> Lemma
		         (requires (True))
			 (ensures (preserves_live h0 h0))
			 [SMTPat (preserves_live h0 h0)]

val preserves_live_trans: h0:mem -> h1:mem -> h2:mem -> Lemma
		         (requires (preserves_live h0 h1 /\ preserves_live h1 h2))
			 (ensures (preserves_live h0 h2))
			 [SMTPat (preserves_live h0 h1);
			  SMTPat (preserves_live h1 h2)]

val modifies_1_refl: #a:Type0 -> #len:size_t -> b:lbuffer a len -> h0:mem -> Lemma
			 (requires (live h0 b))
			 (ensures (modifies1 b h0 h0))
			 [SMTPat (modifies1 b h0 h0)]

val modifies_1_modifies_2: #a1:Type0 -> #a2:Type0 -> #len1:size_t -> #len2:size_t -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> h0:mem -> h1:mem -> Lemma
			 (requires (live h0 b1 /\ live h0 b2 /\ modifies1 b1 h0 h1))
			 (ensures (modifies2 b1 b2 h0 h1 /\ modifies2 b2 b1 h0 h1))
			 [SMTPat (modifies1 b1 h0 h1);
			  SMTPat (live h0 b1);
			  SMTPat (live h0 b2)]


val modifies_2_modifies_3: #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len1:size_t -> #len2:size_t -> #len3:size_t -> 
		           b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> h0:mem -> h1:mem -> Lemma
			 (requires (live h0 b1 /\ live h0 b2 /\ live h0 b3 /\ modifies2 b1 b2 h0 h1))
			 (ensures (modifies3 b1 b2 b3 h0 h1 /\ modifies3 b1 b3 b2 h0 h1 /\ modifies3 b2 b1 b3 h0 h1 /\ 
				   modifies3 b2 b3 b1 h0 h1 /\ modifies3 b3 b1 b2 h0 h1 /\ modifies3 b3 b2 b1 h0 h1))
			 [SMTPat (modifies2 b1 b2 h0 h1);
			  SMTPat (live h0 b1);
			  SMTPat (live h0 b2);
			  SMTPat (live h0 b3)]


val modifies_1_trans: #a:Type0 -> #len:size_t -> b:lbuffer a len -> h0:mem -> h1:mem -> h2:mem -> Lemma
			 (requires (live h0 b /\ modifies1 b h0 h1 /\ modifies1 b h1 h2))
			 (ensures (modifies1 b h0 h2))
			 [SMTPat (modifies1 b h0 h1);
			  SMTPat (modifies1 b h1 h2);
			  SMTPat (live h0 b)]


val modifies_2_trans: #a1:Type0 -> #a2:Type0 -> #len1:size_t -> #len2:size_t -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> h0:mem -> h1:mem -> h2:mem -> Lemma
			 (requires (live h0 b1 /\ live h0 b2 /\ modifies2 b1 b2 h0 h1 /\ modifies2 b1 b2 h1 h2))
			 (ensures (modifies2 b1 b2 h0 h2))
			 [SMTPat (modifies2 b1 b2 h0 h1);
			  SMTPat (modifies2 b1 b2 h1 h2);
			  SMTPat (live h0 b1);
			  SMTPat (live h0 b2)]

val modifies_3_trans: #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len1:size_t -> #len2:size_t -> #len3:size_t -> 
		           b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> h0:mem -> h1:mem -> h2:mem -> Lemma
			 (requires (live h0 b1 /\ live h0 b2 /\ live h0 b3 /\ modifies3 b1 b2 b3 h0 h1 /\ modifies3 b1 b2 b3 h1 h2))
			 (ensures (modifies3 b1 b2 b3 h0 h2))
			 [SMTPat (modifies3 b1 b2 b3 h0 h1);
			  SMTPat (modifies3 b1 b2 b3 h1 h2);
			  SMTPat (live h0 b1);
			  SMTPat (live h0 b2);
			  SMTPat (live h0 b3)]


val modifies1_lemma:  #a1:Type0 -> #a2:Type0 -> #len1:size_t -> #len2:size_t -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> h0:mem -> h1:mem -> Lemma
			 (requires (disjoint b1 b2 /\ live h0 b1 /\ modifies1 b2 h0 h1))
			 (ensures  (live h1 b1 /\ as_lseq b1 h1 == as_lseq b1 h0))
			 [SMTPat (disjoint b1 b2);
			  SMTPat (live h0 b1);
			  SMTPat (modifies1 b2 h0 h1)]


val modifies2_lemma:  #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len1:size_t -> #len2:size_t -> #len3:size_t -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> h0:mem -> h1:mem -> Lemma
			 (requires (disjoint b1 b2 /\ disjoint b1 b3 /\ live h0 b1 /\ modifies2 b2 b3 h0 h1))
			 (ensures  (live h1 b1 /\ as_lseq b1 h1 == as_lseq b1 h0))
			 [SMTPat (disjoint b1 b2);
			  SMTPat (disjoint b1 b3);
			  SMTPat (live h0 b1);
			  SMTPat (modifies2 b2 b3 h0 h1)]


val modifies3_lemma:  #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #a4:Type0-> #len1:size_t -> #len2:size_t -> #len3:size_t -> #len4:size_t -> 
		      b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> b4:lbuffer a4 len4 -> h0:mem -> h1:mem -> Lemma
			 (requires (disjoint b1 b2 /\ disjoint b1 b3 /\ disjoint b1 b4 /\ live h0 b1 /\ modifies3 b2 b3 b4 h0 h1))
			 (ensures  (live h1 b1 /\ as_lseq b1 h1 == as_lseq b1 h0))
			 [SMTPat (disjoint b1 b2);
			  SMTPat (disjoint b1 b3);
			  SMTPat (disjoint b1 b4);
			  SMTPat (live h0 b1);
			  SMTPat (modifies3 b2 b3 b4 h0 h1)]


val modifies_sub_lemma: #a:Type0 -> #len:size_t -> b:lbuffer a len -> start:size_t -> n:size_t{start+n <= len} -> h0:mem -> h1:mem -> Lemma
			 (requires (live h0 b /\ modifies1 (sub b start n) h0 h1))
			 (ensures  (modifies1 b h0 h1 /\ as_lseq b h1 == LSeq.update_sub (as_lseq b h0) start n (LSeq.sub (as_lseq b h1) start n)))
			 [SMTPat (live h0 b);
			  SMTPat (modifies1 (sub b start n) h0 h1)]

val create: #a:Type0 -> len:size_t -> init:a -> Stack (lbuffer a len)
		      (requires (fun h0 -> True))
		      (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ 
					    creates1 r h0 h1 /\ 
					    modifies1 r h0 h1 /\ 
					    as_lseq #a #len r h1 == LSeq.create #a len init))
		      
val createL: #a:Type0 -> init:list a{List.Tot.length init <= max_size_t} -> Stack (lbuffer a (List.Tot.length init))
		      (requires (fun h0 -> True))
		      (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ creates1 r h0 h1 /\ modifies1 r h0 h1 /\ as_lseq #a #(List.Tot.length init) r h1 == LSeq.createL #a init))

val alloc: #a:Type0 -> #b:Type0 -> len:size_t -> init:a -> 
		 bufs:list bufitem ->
		 spec:(h0:mem -> r:b -> h1:mem -> Type) ->
		 impl:(buf:lbuffer a len -> Stack b
			   (requires (fun h -> live h buf /\ live_list h bufs /\ disjoint_list buf bufs))
			   (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
						 modifies (BufItem buf :: bufs) h0 h1 /\
						 spec h0 r h1))) ->
		    Stack b
		      (requires (fun h0 -> True))
		      (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ 
					    modifies bufs h0 h1 /\
					    spec h0 r h1))


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

val blit: #a:Type -> #len:size_t -> i:lbuffer a len -> start1:size_t -> 
          o:lbuffer a len -> start2:size_t -> 
	  num:size_t{start1 + num <= len /\ start2 + num <= len} -> Stack unit 
 		  (requires (fun h0 -> live h0 i /\ live h0 o ))
  		  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ 
		  			modifies1 o h0 h1 /\ 
					as_lseq o h1 == 
					   LSeq.update_sub (as_lseq o h0) 
						start1 num
						(LSeq.sub (as_lseq i h0) start2 num)))

val copy: #a:Type -> #len:size_t -> i:lbuffer a len -> o:lbuffer a len -> Stack unit 
 		  (requires (fun h0 -> live h0 i /\ live h0 o ))
  		  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ 
		  			modifies1 o h0 h1 /\ 
					as_lseq o h1 == as_lseq i h0))


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
	    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 input h0 h1 /\
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
	    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 input h0 h1 /\
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
	    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 input h0 h1 /\
				  as_lseq #a #len input h1 ==  LSeq.repeat_range start fin spec (as_lseq #a #len input h0)))


val uints_from_bytes_le: 
  #t:inttype -> #len:size_t{len `op_Multiply` numbytes t <= max_size_t} -> 
  o:lbuffer (uint_t t) len ->
  i:lbuffer uint8 (len `op_Multiply` numbytes t) -> 
  Stack unit 
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 == 
			      (LSeq.uints_from_bytes_le #t #len (as_lseq i h0) )))


val uint32s_from_bytes_le: 
  #len:size_t{len `op_Multiply` 4 <= max_size_t} -> 
  o:lbuffer uint32 len ->
  i:lbuffer uint8 (len `op_Multiply` 4) -> 
  Stack unit 
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 == 
			      (LSeq.uints_from_bytes_le #U32 #len (as_lseq i h0) )))

val uint32s_to_bytes_le: 
  #len:size_t{len `op_Multiply` 4 <= max_size_t} -> 
  o:lbuffer uint8 (len `op_Multiply` 4) -> 
  i:lbuffer uint32 len ->
  Stack unit 
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 == 
			      (LSeq.uints_to_bytes_le #U32 #len (as_lseq i h0) )))


let op_Array_Assignment = upd
let op_Array_Access = index
