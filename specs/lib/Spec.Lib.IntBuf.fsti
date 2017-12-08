module Spec.Lib.IntBuf

open FStar.HyperStack
open FStar.HyperStack.ST
open Spec.Lib.IntTypes

module LSeq = Spec.Lib.IntSeq


inline_for_extraction val lbuffer: a:Type0 -> len:size_t -> Type0
inline_for_extraction val sub: #a:Type0 -> #len:size_t -> b:lbuffer a len -> start:size_t -> n:size_t{start + n <= len} -> Tot (lbuffer a n)
 let slice #a #len (b:lbuffer a len) (start:size_t) (fin:size_t{fin <= len /\ start <= fin}) = sub #a #len b start (fin - start)
noeq type bufitem = | BufItem: #a:Type0 -> #len:size_t -> buf:lbuffer a len -> bufitem


inline_for_extraction val disjoint: #a1:Type0 -> #a2:Type0 -> #len1:size_t -> #len2:size_t -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> GTot Type0
inline_for_extraction val live: #a:Type0 -> #len:size_t ->  mem -> lbuffer a len -> GTot Type0
inline_for_extraction val preserves_live: mem -> mem -> GTot Type0
inline_for_extraction val as_lseq: #a:Type0 -> #len:size_t -> lbuffer a len -> mem -> GTot (LSeq.lseq a len)

 let creates1 (#a:Type0) (#len:size_t) (b:lbuffer a len) (h0:mem) (h1:mem) : GTot Type = 
 (live h1 b /\
  (forall (a':Type0) (len':size_t) (b':lbuffer a' len'). {:pattern (live h0 b')} live h0 b' ==> (live h1 b' /\ disjoint b b'  /\ disjoint b' b)))
  
 let rec creates (l:list bufitem) (h0:mem) (h1:mem) : GTot Type = 
  match l with
  | [] -> True
  | b::t -> creates1 b.buf h0 h1 /\ creates t h0 h1
  
inline_for_extraction val modifies1: #a:Type0 -> #len:size_t ->  lbuffer a len -> mem -> mem -> GTot Type0

inline_for_extraction val modifies2: #a1:Type0 -> #a2:Type0 -> #len1:size_t -> #len2:size_t -> lbuffer a1 len1 -> lbuffer a2 len2 -> mem -> mem -> GTot Type0

inline_for_extraction val modifies3: #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len1:size_t -> #len2:size_t -> #len3:size_t -> lbuffer a1 len1 -> lbuffer a2 len2 -> lbuffer a3 len3 -> mem -> mem -> GTot Type0

inline_for_extraction val modifies: list bufitem -> mem -> mem -> GTot Type0

inline_for_extraction val live_list: mem -> list bufitem -> GTot Type0

inline_for_extraction val disjoint_list: #a:Type0 -> #len:size_t -> b:lbuffer a len -> list bufitem  -> GTot Type0


inline_for_extraction val create: #a:Type0 -> len:size_t -> init:a -> StackInline (lbuffer a len)
		      (requires (fun h0 -> True))
		      (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ 
					    creates1 r h0 h1 /\ 
					    modifies1 r h0 h1 /\ 
					    as_lseq #a #len r h1 == LSeq.create #a len init))
		      
inline_for_extraction val createL: #a:Type0 -> init:list a{List.Tot.length init <= max_size_t} -> StackInline (lbuffer a (List.Tot.length init))
		      (requires (fun h0 -> True))
		      (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ creates1 r h0 h1 /\ modifies1 r h0 h1 /\ as_lseq #a #(List.Tot.length init) r h1 == LSeq.createL #a init))

inline_for_extraction val alloc: #a:Type0 -> #b:Type0 -> len:size_t -> init:a -> 
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


inline_for_extraction val index: #a:Type0 -> #len:size_t -> b:lbuffer a len -> i:size_t{i < len} -> Stack a 
		      (requires (fun h0 -> live h0 b))
		      (ensures (fun h0 r h1 -> h0 == h1 /\ r == LSeq.index #a #len (as_lseq #a #len b h0) i)) 

inline_for_extraction val upd: #a:Type0 -> #len:size_t -> b:lbuffer a len -> i:size_t{i < len} -> v:a -> Stack unit 
		      (requires (fun h0 -> live h0 b /\ len > 0))
		      (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ modifies1 b h0 h1 /\ as_lseq #a #len b h1 == LSeq.upd #a #len (as_lseq #a #len b h0) i v))

inline_for_extraction let op_Array_Assignment = upd
inline_for_extraction let op_Array_Access = index

noextract
 val map: #a:Type -> #len:size_t -> f:(a -> Tot a) -> b:lbuffer a len -> Stack unit 
		      (requires (fun h0 -> live h0 b))
		      (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 b h0 h1 /\ as_lseq #a #len b h1 == LSeq.map #a #a #len f (as_lseq #a #len b h0)))

noextract
 val map2: #a1:Type -> #a2:Type -> #len:size_t -> f:(a1 -> a2 -> Tot a1) -> b1:lbuffer a1 len -> b2:lbuffer a2 len -> Stack unit 
		      (requires (fun h0 -> live h0 b1 /\ live h0 b2))
		      (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 b1 h0 h1 /\ as_lseq #a1 #len b1 h1 == LSeq.map2 #a1 #a2 #a1 #len f (as_lseq #a1 #len b1 h0) (as_lseq #a2 #len b2 h0)))

noextract val blit: #a:Type -> #len:size_t -> i:lbuffer a len -> start1:size_t -> 
          o:lbuffer a len -> start2:size_t -> 
	  num:size_t{start1 + num <= len /\ start2 + num <= len} -> Stack unit 
 		  (requires (fun h0 -> live h0 i /\ live h0 o ))
  		  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ 
		  			modifies1 o h0 h1 /\ 
					as_lseq o h1 == 
					   LSeq.update_sub (as_lseq o h0) 
						start1 num
						(LSeq.sub (as_lseq i h0) start2 num)))

noextract val copy: #a:Type -> #len:size_t -> i:lbuffer a len -> o:lbuffer a len -> Stack unit 
 		  (requires (fun h0 -> live h0 i /\ live h0 o ))
  		  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ 
		  			modifies1 o h0 h1 /\ 
					as_lseq o h1 == as_lseq i h0))


noextract val repeat: #a:Type -> #b:Type -> #lift:(mem -> b -> GTot (option a)) -> 
	    n:size_t -> spec:(a -> Tot a) -> 
	    impl:(x:b -> Stack unit (requires (fun h0 -> Some? (lift h0 x))) (ensures (fun h0 _ h1 -> Some? (lift h0 x) /\ Some? (lift h1 x) /\ Some?.v (lift h1 x) == spec (Some?.v (lift h0 x))))) ->
	    input:b ->
	    Stack unit
	    (requires (fun h0 -> Some? (lift h0 input)))
	    (ensures (fun h0 _ h1 -> Some? (lift h0 input) /\ Some? (lift h1 input) /\
				  Some?.v (lift h1 input) ==  LSeq.repeat n spec (Some?.v (lift h0 input))))


noextract val repeat_range: #a:Type -> #b:Type -> #lift:(mem -> b -> GTot (option a)) -> 
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

noextract val repeati: #a:Type -> #b:Type -> #lift:(mem -> b -> GTot (option a)) -> 
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

noextract val iter: #a:Type -> #len:size_t -> n:size_t -> spec:(LSeq.lseq a len -> Tot (LSeq.lseq a len)) -> 
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

noextract val iteri: #a:Type -> #len:size_t -> n:size_t -> spec:(i:size_t{i < n}  -> LSeq.lseq a len -> Tot (LSeq.lseq a len)) -> 
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

noextract val iter_range: #a:Type -> #len:size_t -> start:size_t -> fin:size_t{start <= fin} ->
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


noextract val uints_from_bytes_le: 
  #t:inttype -> #len:size_t{len `op_Multiply` numbytes t <= max_size_t} -> 
  o:lbuffer (uint_t t) len ->
  i:lbuffer uint8 (len `op_Multiply` numbytes t) -> 
  Stack unit 
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 == 
			      (LSeq.uints_from_bytes_le #t #len (as_lseq i h0) )))


noextract val uint32s_from_bytes_le: 
  #len:size_t{len `op_Multiply` 4 <= max_size_t} -> 
  o:lbuffer uint32 len ->
  i:lbuffer uint8 (len `op_Multiply` 4) -> 
  Stack unit 
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 == 
			      (LSeq.uints_from_bytes_le #U32 #len (as_lseq i h0) )))

noextract val uint32s_to_bytes_le: 
  #len:size_t{len `op_Multiply` 4 <= max_size_t} -> 
  o:lbuffer uint8 (len `op_Multiply` 4) -> 
  i:lbuffer uint32 len ->
  Stack unit 
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 == 
			      (LSeq.uints_to_bytes_le #U32 #len (as_lseq i h0) )))



