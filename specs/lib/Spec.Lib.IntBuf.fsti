module Spec.Lib.IntBuf

open FStar.HyperStack
open FStar.HyperStack.ST
open Spec.Lib.IntTypes

module LSeq = Spec.Lib.IntSeq

unfold
let v = size_v
inline_for_extraction val lbuffer: a:Type0 -> len:size_nat -> Type0
inline_for_extraction val sub: #a:Type0 -> #len:size_nat -> #olen:size_nat ->  b:lbuffer a len -> start:size_t -> n:size_t{v start + v n <= len /\ v n == olen} -> Tot (lbuffer a olen)
 let slice #a #len #olen (b:lbuffer a (len)) (start:size_t) (fin:size_t{v fin <= len /\ v start <= v fin /\ v fin - v start == olen}) = sub #a #len #olen b start (sub_mod #SIZE fin start)
noeq type bufitem = | BufItem: #a:Type0 -> #len:size_nat -> buf:lbuffer a (len) -> bufitem


inline_for_extraction val disjoint: #a1:Type0 -> #a2:Type0 -> #len1:size_nat -> #len2:size_nat -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> GTot Type0
inline_for_extraction val live: #a:Type0 -> #len:size_nat ->  mem -> lbuffer a len -> GTot Type0
inline_for_extraction val preserves_live: mem -> mem -> GTot Type0
inline_for_extraction val as_lseq: #a:Type0 -> #len:size_nat -> lbuffer a len -> mem -> GTot (LSeq.lseq a len)

 let creates1 (#a:Type0) (#len:size_nat) (b:lbuffer a (len)) (h0:mem) (h1:mem) : GTot Type =
 (live h1 b /\
  (forall (a':Type0) (len':size_nat) (b':lbuffer a' (len')). {:pattern (live h0 b')} live h0 b' ==> (live h1 b' /\ disjoint b b'  /\ disjoint b' b)))

 let rec creates (l:list bufitem) (h0:mem) (h1:mem) : GTot Type =
  match l with
  | [] -> True
  | b::t -> creates1 b.buf h0 h1 /\ creates t h0 h1

inline_for_extraction val modifies1: #a:Type0 -> #len:size_nat ->  lbuffer a (len) -> mem -> mem -> GTot Type0

inline_for_extraction val modifies2: #a1:Type0 -> #a2:Type0 -> #len1:size_nat -> #len2:size_nat -> lbuffer a1 (len1) -> lbuffer a2 (len2) -> mem -> mem -> GTot Type0

inline_for_extraction val modifies3: #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat -> lbuffer a1 (len1) -> lbuffer a2 (len2) -> lbuffer a3 (len3) -> mem -> mem -> GTot Type0

inline_for_extraction val modifies: list bufitem -> mem -> mem -> GTot Type0

inline_for_extraction val live_list: mem -> list bufitem -> GTot Type0

inline_for_extraction val disjoint_list: #a:Type0 -> #len:size_nat -> b:lbuffer a (len) -> list bufitem  -> GTot Type0


inline_for_extraction val create: #a:Type0 -> #len:size_nat -> clen:size_t{v clen == len} -> init:a -> StackInline (lbuffer a len)
		      (requires (fun h0 -> True))
		      (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
					    creates1 r h0 h1 /\
					    modifies1 r h0 h1 /\
					    as_lseq #a #len r h1 == LSeq.create #a len init))

inline_for_extraction val createL: #a:Type0 -> init:list a{List.Tot.length init <= max_size_t} -> StackInline (lbuffer a (List.Tot.length init))
		      (requires (fun h0 -> True))
		      (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ creates1 r h0 h1
				          /\ modifies1 r h0 h1
					  /\ as_lseq r h1 == LSeq.createL #a init))

inline_for_extraction val alloc: #a:Type0 -> #b:Type0 -> #len:size_nat -> clen:size_t{v clen == len} -> init:a ->
		 reads:list bufitem ->
		 writes:list bufitem ->
		 spec:(h0:mem -> r:b -> h1:mem -> Type) ->
		 impl:(buf:lbuffer a len -> Stack b
			   (requires (fun h -> live h buf /\ live_list h reads /\ live_list h writes /\ disjoint_list buf reads /\ disjoint_list buf writes))
			   (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
						 modifies (BufItem buf :: writes) h0 h1 /\
						 spec h0 r h1))) ->
		    Stack b
		      (requires (fun h0 -> live_list h0 reads /\ live_list h0 writes))
		      (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
					    modifies writes h0 h1 /\
					    spec h0 r h1))


inline_for_extraction val index: #a:Type0 -> #len:size_nat -> b:lbuffer a (len) -> i:size_t{v i < len} -> Stack a
		      (requires (fun h0 -> live h0 b))
		      (ensures (fun h0 r h1 -> h0 == h1 /\ r == LSeq.index #a #(len) (as_lseq #a #len b h0) (v i)))

inline_for_extraction val upd: #a:Type0 -> #len:size_nat -> b:lbuffer a (len) -> i:size_t{v i < len} -> x:a -> Stack unit
		      (requires (fun h0 -> live h0 b /\ len > 0))
		      (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ modifies1 b h0 h1
			       /\ as_lseq #a #len b h1 == LSeq.upd #a #(len) (as_lseq #a #len b h0) (v i) x))

inline_for_extraction let op_Array_Assignment #a #len = upd #a #len
inline_for_extraction let op_Array_Access #a #len = index #a #len

val map: #a:Type -> #len:size_nat -> clen:size_t{v clen == len} -> f:(a -> Tot a) -> b:lbuffer a (len) -> Stack unit
		      (requires (fun h0 -> live h0 b))
		      (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 b h0 h1
				  /\ as_lseq #a #len b h1 == LSeq.map #a #a #(len) f (as_lseq #a #len b h0)))

inline_for_extraction
val map2: #a1:Type -> #a2:Type -> #len:size_nat -> clen:size_t{v clen == len} -> f:(a1 -> a2 -> Tot a1) -> b1:lbuffer a1 len -> b2:lbuffer a2 len -> Stack unit
		      (requires (fun h0 -> live h0 b1 /\ live h0 b2))
		      (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 b1 h0 h1 /\ as_lseq #a1 #len b1 h1 == LSeq.map2 #a1 #a2 #a1 #len f (as_lseq #a1 #len b1 h0) (as_lseq #a2 #len b2 h0)))

inline_for_extraction
val copy: #a:Type -> #len:size_nat -> clen:size_t{v clen == len} -> i:lbuffer a len -> o:lbuffer a len -> Stack unit
 		  (requires (fun h0 -> live h0 i /\ live h0 o ))
  		  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
		  			modifies1 o h0 h1 /\
					as_lseq o h1 == as_lseq i h0))


inline_for_extraction
val iter_range: #a:Type -> #len:size_nat -> start:size_t -> fin:size_t{v start <= v fin} ->
         spec:(i:size_nat{v start <= i /\ i < v fin}  -> LSeq.lseq a (len) -> Tot (LSeq.lseq a (len))) ->
         impl:(i:size_t{v start <= v i /\ v i < v fin}  -> x:lbuffer a (len) -> Stack unit
			(requires (fun h0 -> live h0 x))
			(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
				              modifies1 x h0 h1 /\
					      as_lseq #a #len x h1 == spec (v i) (as_lseq #a #len x h0)))) ->
	    input:lbuffer a (len) ->
	    Stack unit
	    (requires (fun h0 -> live h0 input))
	    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 input h0 h1 /\
				  as_lseq #a #len input h1 ==  LSeq.repeat_range (v start) (v fin) spec (as_lseq #a #len input h0)))

inline_for_extraction
val iteri: #a:Type -> #len:size_nat -> n:size_t -> spec:(i:size_nat{i < v n}  -> LSeq.lseq a (len) -> Tot (LSeq.lseq a (len))) ->
         impl:(i:size_t{v i < v n}  -> x:lbuffer a (len) -> Stack unit
			(requires (fun h0 -> live h0 x))
			(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
				              modifies1 x h0 h1 /\
					      as_lseq #a #len x h1 == spec (v i) (as_lseq #a #len x h0)))) ->
	    input:lbuffer a (len) ->
	    Stack unit
	    (requires (fun h0 -> live h0 input))
	    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 input h0 h1 /\
				  as_lseq #a #len input h1 ==  LSeq.repeati (v n) spec (as_lseq #a #len input h0)))

inline_for_extraction
val iter: #a:Type -> #len:size_nat -> n:size_t -> spec:(LSeq.lseq a (len) -> LSeq.lseq a (len)) ->
         impl:(x:lbuffer a (len) -> Stack unit
			(requires (fun h0 -> live h0 x))
			(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
				              modifies1 x h0 h1 /\
					      as_lseq #a #len x h1 == spec (as_lseq #a #len x h0)))) ->
	    input:lbuffer a (len) ->
	    Stack unit
	    (requires (fun h0 -> live h0 input))
	    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 input h0 h1 /\
				  as_lseq #a #len input h1 ==  LSeq.repeat (v n) spec (as_lseq #a #len input h0)))



(*
val repeat: #a:Type -> #b:Type -> #lift:(mem -> b -> GTot (option a)) ->
	    n:size_t -> spec:(a -> Tot a) ->
	    impl:(x:b -> Stack unit (requires (fun h0 -> Some? (lift h0 x))) (ensures (fun h0 _ h1 -> Some? (lift h0 x) /\ Some? (lift h1 x) /\ Some?.v (lift h1 x) == spec (Some?.v (lift h0 x))))) ->
	    input:b ->
	    Stack unit
	    (requires (fun h0 -> Some? (lift h0 input)))
	    (ensures (fun h0 _ h1 -> Some? (lift h0 input) /\ Some? (lift h1 input) /\
				  Some?.v (lift h1 input) ==  LSeq.repeat (v n) spec (Some?.v (lift h0 input))))


val repeat_range: #a:Type -> #b:Type -> #lift:(mem -> b -> GTot (option a)) ->
	    start:size_t -> fin:size_t{v start <= v fin} -> spec:(i:size_nat{v start <= i /\ i < v fin} -> a -> Tot a) ->
	    impl:(i:size_t{v start <= v i /\ v i < v fin} -> x:b -> Stack unit
				   (requires (fun h0 -> Some? (lift h0 x)))
				   (ensures (fun h0 _ h1 -> Some? (lift h0 x) /\ Some? (lift h1 x) /\
							 Some?.v (lift h1 x) == spec (v i) (Some?.v (lift h0 x))))) ->
	    input:b ->
	    Stack unit
	    (requires (fun h0 -> Some? (lift h0 input)))
	    (ensures (fun h0 _ h1 -> Some? (lift h0 input) /\ Some? (lift h1 input) /\
				  Some?.v (lift h1 input) ==  LSeq.repeat_range (v start) (v fin) spec (Some?.v (lift h0 input))))

val repeati: #a:Type -> #b:Type -> #lift:(mem -> b -> GTot (option a)) ->
	    n:size_t -> spec:(i:size_nat{i < v n} -> a -> Tot a) ->
	    impl:(i:size_t{v i < v n} -> x:b -> Stack unit
				   (requires (fun h0 -> Some? (lift h0 x)))
				   (ensures (fun h0 _ h1 -> Some? (lift h0 x) /\ Some? (lift h1 x) /\
							 Some?.v (lift h1 x) == spec (v i) (Some?.v (lift h0 x))))) ->
	    input:b ->
	    Stack unit
	    (requires (fun h0 -> Some? (lift h0 input)))
	    (ensures (fun h0 _ h1 -> Some? (lift h0 input) /\ Some? (lift h1 input) /\
				  Some?.v (lift h1 input) ==  LSeq.repeati (v n) spec (Some?.v (lift h0 input))))

*)
