module Lib.Buffer

open FStar.HyperStack
open FStar.HyperStack.ST
open Lib.IntTypes

module LSeq = Lib.Sequence


unfold let v = size_v

let buffer a = LowStar.Buffer.buffer a
//inline_for_extraction val buffer: a:Type0 -> Type0
inline_for_extraction val length: #a:Type0 -> buffer a -> GTot size_nat
inline_for_extraction let lbuffer (a:Type0) (len:size_nat) = b:buffer a{length b == len}

inline_for_extraction val gsub: #a:Type0 -> #len:size_nat -> #olen:size_nat ->  b:lbuffer a len -> start:size_t -> n:size_t{v start + v n <= len /\ v n == olen} -> GTot (lbuffer a olen)
let gslice #a #len #olen (b:lbuffer a (len)) (start:size_t) (fin:size_t{v fin <= len /\ v start <= v fin /\ v fin - v start == olen}) = gsub #a #len #olen b start (sub_mod #SIZE fin start)
noeq type bufitem = | BufItem: #a:Type0 -> #len:size_nat -> buf:lbuffer a (len) -> bufitem

inline_for_extraction val disjoint: #a1:Type0 -> #a2:Type0 -> #len1:size_nat -> #len2:size_nat -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> GTot Type0
inline_for_extraction val live: #a:Type0 -> mem -> buffer a -> GTot Type0
inline_for_extraction val preserves_live: mem -> mem -> GTot Type0
inline_for_extraction val as_seq: #a:Type0 -> #len:size_nat -> b:lbuffer a len -> h:mem -> GTot (s:LSeq.seq a{LSeq.length s == len})
inline_for_extraction val as_lseq: #a:Type0 -> #len:size_nat -> b:lbuffer a len -> h:mem -> GTot (s:LSeq.lseq a len{s == as_seq b h})

let creates1 (#a:Type0) (#len:size_nat) (b:lbuffer a (len)) (h0:mem) (h1:mem) : GTot Type =
 (live h1 b /\
  (forall (a':Type0) (len':size_nat) (b':lbuffer a' (len')). {:pattern (live h0 b')} live h0 b' ==> (live h1 b' /\ disjoint b b'  /\ disjoint b' b)))

let creates2 (#a0:Type0) (#a1:Type0) (#len0:size_nat) (#len1:size_nat) (b0:lbuffer a0 len0) (b1:lbuffer a1 len1) (h0:mem) (h1:mem) : GTot Type =
 (live h1 b0 /\ live h1 b1 /\ disjoint b0 b1 /\
  (forall (a':Type0) (len':size_nat) (b':lbuffer a' (len')). {:pattern (live h0 b')} live h0 b' ==> (live h1 b' /\ disjoint b0 b' /\ disjoint b' b0 /\ disjoint b' b1 /\ disjoint b1 b')))

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
inline_for_extraction val disjoint_lists: list bufitem -> list bufitem  -> GTot Type0
inline_for_extraction val disjoints: list bufitem  -> GTot Type0

inline_for_extraction val sub: #a:Type0 -> #len:size_nat -> #olen:size_nat ->  b:lbuffer a len -> start:size_t -> n:size_t{v start + v n <= len /\ v n == olen} ->
  Stack (lbuffer a olen)
    (requires (fun h0 -> live h0 b))
    (ensures (fun h0 r h1 -> h0 == h1 /\ r == gsub #a #len #olen b start n))

inline_for_extraction val slice: #a:Type0 -> #len:size_nat -> #olen:size_nat ->  b:lbuffer a len -> start:size_t -> fin:size_t{v start <= v fin /\ v fin <= len /\ v fin - v start == olen} ->
  Stack (lbuffer a olen)
    (requires (fun h0 -> live h0 b))
    (ensures (fun h0 r h1 -> h0 == h1 /\ r == gslice #a #len #olen b start fin))

inline_for_extraction val index: #a:Type0 -> #len:size_nat -> b:lbuffer a (len) -> i:size_t{v i < len} ->
  Stack a
    (requires (fun h0 -> live h0 b))
	 (ensures (fun h0 r h1 -> h0 == h1 /\ r == LSeq.index #a #(len) (as_seq b h0) (v i)))

inline_for_extraction val upd: #a:Type0 -> #len:size_nat -> b:lbuffer a (len) -> i:size_t{v i < len} -> x:a ->
  Stack unit
	 (requires (fun h0 -> live h0 b /\ len > 0))
	 (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ modifies1 b h0 h1
		                  /\ as_seq b h1 == LSeq.upd #a #(len) (as_seq b h0) (v i) x))

inline_for_extraction let op_Array_Assignment #a #len = upd #a #len
inline_for_extraction let op_Array_Access #a #len = index #a #len


inline_for_extraction val create: #a:Type0 -> #len:size_nat -> clen:size_t{v clen == len} -> init:a ->
  StackInline (lbuffer a len)
    (requires (fun h0 -> True))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
					           creates1 r h0 h1 /\
					           modifies1 r h0 h1 /\
					           as_seq  r h1 == LSeq.create #a (len) init))

inline_for_extraction val createL: #a:Type0 -> init:list a{List.Tot.length init <= max_size_t} ->
  StackInline (lbuffer a ((List.Tot.length init)))
    (requires (fun h0 -> True))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ creates1 r h0 h1
				            /\ modifies1 r h0 h1
					         /\ as_seq r h1 == LSeq.createL #a init))

inline_for_extraction val createG: #a:Type0 -> init:list a{List.Tot.length init <= max_size_t} ->
  StackInline (lbuffer a ((List.Tot.length init)))
    (requires (fun h0 -> True))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ creates1 r h0 h1
				            /\ modifies1 r h0 h1
					         /\ as_seq r h1 == LSeq.createL #a init))

inline_for_extraction val alloc: #h0:mem -> #a:Type0 -> #b:Type0 -> #w:Type0 -> #len:size_nat -> #wlen:size_nat -> clen:size_t{v clen == len} -> init:a ->
  write:lbuffer w wlen ->
  spec:(h:mem -> GTot(r:b -> LSeq.lseq w (wlen) -> Type)) ->
  impl:(buf:lbuffer a len -> Stack b
    (requires (fun h -> creates1 #a #len buf h0 h /\
		     preserves_live h0 h /\
		     modifies1 buf h0 h /\
		     as_seq buf h == LSeq.create #a (len) init /\
		     live h0 write))
    (ensures (fun h r h' -> preserves_live h h' /\ modifies2 buf write h h' /\
			 spec h0 r (as_seq write h')))) ->
  Stack b
    (requires (fun h -> h == h0 /\ live h write))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
		          modifies1 write h0 h1 /\
		          spec h0 r (as_seq write h1)))


inline_for_extraction val alloc_with: #h0:mem -> #a:Type0 -> #b:Type0 -> #w:Type0 -> #len:size_nat -> #wlen:size_nat -> clen:size_t{v clen == len} ->
  init_spec: LSeq.lseq a len ->
  init:(unit -> StackInline (lbuffer a len)
               (requires (fun h -> h == h0))
               (ensures  (fun h0 r h1 -> creates1 #a #len r h0 h1 /\
		                                preserves_live h0 h1 /\
		                                modifies1 r h0 h1 /\
		                                as_seq r h1 == init_spec))) ->
  write:lbuffer w wlen ->
  spec:(h:mem -> GTot(r:b -> LSeq.lseq w (wlen) -> Type)) ->
  impl:(buf:lbuffer a len -> Stack b
    (requires (fun h -> creates1 #a #len buf h0 h /\
		     preserves_live h0 h /\
		     modifies1 buf h0 h /\
		     as_seq buf h == init_spec /\
		     live h0 write))
    (ensures (fun h r h' -> preserves_live h h' /\ modifies2 buf write h h' /\
			 spec h0 r (as_seq write h')))) ->
  Stack b
    (requires (fun h -> h == h0 /\ live h write))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
		          modifies1 write h0 h1 /\
		          spec h0 r (as_seq write h1)))

inline_for_extraction val alloc_nospec: #h0:mem -> #a:Type0 -> #b:Type0 -> #w:Type0 -> #len:size_nat -> #wlen:size_nat -> clen:size_t{v clen == len} -> init:a ->
  write:lbuffer w wlen ->
  impl:(buf:lbuffer a len -> Stack b
    (requires (fun h -> creates1 #a #len buf h0 h /\
		     preserves_live h0 h /\
		     modifies1 buf h0 h /\
		     live h0 write))
    (ensures (fun h r h' -> preserves_live h h' /\ modifies2 buf write h h'))) ->
  Stack b
    (requires (fun h -> h == h0 /\ live h write))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
		          modifies1 write h0 h1))

(* (\** This function will allocate one buffer, write it and write in 2 other buffers, *)
(*     the value of the first 'write' buffer is functionnally caracterized while the *)
(*     functionnal behavior of the second 'write2' buffer is discarded *)
(* *\) *)
(* inline_for_extraction val alloc_write2_discard: #h0:mem -> #a:Type0 -> #b:Type0 -> #w:Type0 -> #w2:Type0 -> #len:size_nat -> #wlen:size_nat -> #wlen2:size_nat -> clen:size_t{v clen == len} -> init:a -> *)
(*   write:lbuffer w wlen -> *)
(*   write2:lbuffer w2 wlen2 -> *)
(*   spec:(h:mem -> GTot(r:b -> LSeq.lseq w (wlen) -> Type)) -> *)
(*   impl:(buf:lbuffer a len -> Stack b *)
(*     (requires (fun h -> creates1 #a #len buf h0 h /\ *)
(*               live h0 write /\ live h0 write2 *)
(*               /\ disjoint write write2 /\ disjoint write2 write /\ *)
(* 		          preserves_live h0 h /\ *)
(* 		          modifies1 buf h0 h /\ *)
(* 	             as_seq buf h == LSeq.create #a (len) init)) *)
(*     (ensures (fun h r h' -> preserves_live h h' /\ modifies3 buf write write2 h h' /\ *)
(* 			 spec h0 r (as_seq write h')))) -> *)
(*   Stack b *)
(*     (requires (fun h -> h == h0 /\ live h write /\ live h write2)) *)
(*     (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ *)
(* 		          modifies2 write write2 h0 h1 /\ *)
(* 		          spec h0 r (as_seq write h1))) *)

(* Various Allocation Patterns *)

val map: #a:Type -> #len:size_nat -> clen:size_t{v clen == len} -> f:(a -> Tot a) -> b:lbuffer a (len) ->
  Stack unit
    (requires (fun h0 -> live h0 b))
	 (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 b h0 h1
				            /\ as_seq  b h1 == LSeq.map #a #a #(len) f (as_seq  b h0)))

inline_for_extraction
val map2: #a1:Type -> #a2:Type -> #len:size_nat -> clen:size_t{v clen == len} -> f:(a1 -> a2 -> Tot a1) -> b1:lbuffer a1 len -> b2:lbuffer a2 len ->
  Stack unit
	 (requires (fun h0 -> live h0 b1 /\ live h0 b2))
	 (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 b1 h0 h1
                        /\ as_seq b1 h1 == LSeq.map2 #a1 #a2 #a1 #(len) f (as_seq b1 h0) (as_seq b2 h0)))

inline_for_extraction
val copy: #a:Type -> #len:size_nat -> o:lbuffer a len -> clen:size_t{v clen == len}  -> i:lbuffer a len ->
  Stack unit
    (requires (fun h0 -> live h0 i /\ live h0 o ))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
                          modifies1 o h0 h1 /\
                          as_seq o h1 == as_seq i h0))




(* EXPERIMENTAL: Various Looping Patterns *)

inline_for_extraction
val iter_range: #a:Type -> #len:size_nat -> start:size_t -> fin:size_t{v start <= v fin} ->
  spec:(i:size_nat{v start <= i /\ i < v fin}  -> LSeq.lseq a (len) -> Tot (LSeq.lseq a (len))) ->
  impl:(i:size_t{v start <= v i /\ v i < v fin}  -> x:lbuffer a (len) -> Stack unit
    (requires (fun h0 -> live h0 x))
	 (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
				              modifies1 x h0 h1 /\
					           as_seq  x h1 == spec (v i) (as_seq  x h0)))) ->
  input:lbuffer a (len) ->
  Stack unit
	 (requires (fun h0 -> live h0 input))
	 (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 input h0 h1 /\
				              as_seq  input h1 ==  LSeq.repeat_range (v start) (v fin) spec (as_seq  input h0)))


inline_for_extraction
val iteri: #a:Type -> #len:size_nat -> n:size_t ->
  spec:(i:size_nat{i < v n}  -> LSeq.lseq a (len) -> Tot (LSeq.lseq a (len))) ->
  impl:(i:size_t{v i < v n}  -> x:lbuffer a (len) -> Stack unit
    (requires (fun h0 -> live h0 x))
	 (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
				              modifies1 x h0 h1 /\
					           as_seq  x h1 == spec (v i) (as_seq  x h0)))) ->
  input:lbuffer a (len) ->
  Stack unit
	 (requires (fun h0 -> live h0 input))
	 (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 input h0 h1 /\
				              as_seq  input h1 ==  LSeq.repeati (v n) spec (as_seq  input h0)))


inline_for_extraction
val iter: #a:Type -> #len:size_nat -> #clen:size_t{v clen == len} -> n:size_t ->
  spec:(LSeq.lseq a len -> LSeq.lseq a len) ->
  impl:(x:lbuffer a len -> Stack unit
    (requires (fun h0 -> live h0 x))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			  modifies1 x h0 h1 /\
			 as_seq  x h1 == spec (as_lseq  x h0)))) ->
  input:lbuffer a len ->
  Stack unit
    (requires (fun h0 -> live h0 input))
	 (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 input h0 h1 /\
		               as_seq  input h1 ==  LSeq.repeat (v n) spec (as_seq  input h0)))


let loop_inv (h0:mem) (h1:mem) (#a:Type) (len:size_nat) (n:size_t)  (buf:lbuffer a len)
  (spec:(h:mem -> GTot (i:size_nat{i < v n} -> LSeq.lseq a (len) -> Tot (LSeq.lseq a (len))))) (i:size_t{v i <= v n}) : Type =
  live h0 buf /\ preserves_live h0 h1
  /\ modifies1 buf h0 h1
  /\ (let b0 = as_seq  buf h0 in
    let b1 = as_seq  buf h1 in
    b1 == LSeq.repeati #(LSeq.lseq a (len)) (v i) (spec h0) b0)

inline_for_extraction
val loop:
  #h0:mem ->
  #a:Type0 ->
  #len:size_nat ->
  n:size_t ->
  buf:lbuffer a len ->
  spec:(h:mem -> GTot (i:size_nat{i < v n} -> LSeq.lseq a (len) -> Tot (LSeq.lseq a (len)))) ->
  impl:(i:size_t{v i < v n} -> Stack unit
    (requires (fun h -> loop_inv h0 h #a len n buf spec i))
    (ensures (fun _ _ h1 -> loop_inv h0 h1 #a len n buf spec (i +. size 1)))) ->
  Stack unit
	 (requires (fun h -> live h buf /\ h0 == h))
	 (ensures (fun _ _ h1 -> preserves_live h0 h1
                       /\ modifies1 buf h0 h1
                       /\ (let b0 = as_seq  buf h0 in
                       let b1 = as_seq  buf h1 in
                       b1 == LSeq.repeati #(LSeq.lseq a (len)) (v n) (spec h0) b0)))


inline_for_extraction
val loop_set:
  #a:Type0 ->
  #len:size_nat ->
  buf:lbuffer a len ->
  start:size_t ->
  n:size_t{v n + v start <= len} ->
  init:a ->
  Stack unit
	 (requires (fun h -> live h buf))
	 (ensures (fun h0 _ h1 -> preserves_live h0 h1
                       /\ modifies1 buf h0 h1
                       /\ LSeq.sub #a #(len) (as_seq buf h1) (v start) (v n) == LSeq.create #a (len) init))


let loop_nospec_inv (h0:mem) (h1:mem) (#a:Type) (len:size_nat) (n:size_nat)  (buf:lbuffer a len) (i:size_nat{i <= n}) : Type =
  live h0 buf /\ preserves_live h0 h1
  /\ modifies1 buf h0 h1


inline_for_extraction
val loop_nospec:
  #h0:mem ->
  #a:Type0 ->
  #len:size_nat ->
  n:size_t ->
  buf:lbuffer a len ->
  impl:(i:size_t{v i < v n} -> Stack unit
    (requires (fun h -> loop_nospec_inv h0 h #a len (v n) buf (v i)))
	 (ensures (fun _ _ h1 -> loop_nospec_inv h0 h1 #a len (v n) buf (v i + 1)))) ->
  Stack unit
	 (requires (fun h -> live h buf /\ h0 == h))
	 (ensures (fun _ _ h1 -> preserves_live h0 h1
                       /\ modifies1 buf h0 h1))

open FStar.Mul

#reset-options "--z3rlimit 5000 --max_fuel 0"
inline_for_extraction
val map_blocks: #h0:mem ->
		#a:Type0 ->
		#bs:size_nat{bs > 0} ->
		#nb:size_nat{nb * bs <= maxint SIZE} ->
		blocksize:size_t{size_v blocksize == bs} ->
		nblocks:size_t{size_v nblocks == nb} ->
		buf:lbuffer a (nb * bs) ->
		f_spec:(mem -> GTot (i:size_nat{i + 1 <= nb} -> LSeq.lseq a bs -> LSeq.lseq a bs)) ->
		f:(i:size_t{size_v i + 1 <= v nblocks} -> Stack unit
				  (requires (fun h -> live h buf /\
						   preserves_live h0 h /\
				                   modifies1 buf h0 h))
				  (ensures (fun h _ h' ->
						   preserves_live h h' /\
						   (size_v i * v blocksize) + v blocksize <= v (nblocks *. blocksize) /\
						  (let bufi = gsub #a #(nb * bs) #bs buf (i *. blocksize) blocksize in
						   modifies1 bufi h h' /\
						   as_seq bufi h' ==
						   f_spec h (size_v i) (as_seq bufi h))))) ->
		Stack unit
		                  (requires (fun h -> h == h0 /\ live h buf))
				  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 buf h0 h1 /\
							as_seq buf h1 == LSeq.map_blocks #a bs nb (f_spec h0) (as_seq buf h0)))

(*
val map_blocks: #h0:mem ->
		#a:Type0 ->
		#bs:size_t{bs > 0} ->
		#nb:size_t{nb * bs <= maxint SIZE} ->
		blocksize:size_t{size_v blocksize == bs} ->
		nblocks:size_t{size_v nblocks == nb} ->
		f_spec:(mem -> GTot (i:size_t{i + 1 <= nb} -> LSeq.lseq a bs -> LSeq.lseq a bs)) ->
		f:(i:size_t{size_v i + 1 <= nb} -> bufi:lbuffer a bs -> Stack unit
				  (requires (fun h -> live h bufi /\
						   preserves_live h0 h /\
				                   modifies1 bufi h0 h))
				  (ensures (fun h _ h' ->
						   preserves_live h h' /\
						   modifies1 bufi h h' /\
						   as_seq bufi h' ==
						   f_spec h0 (size_v i) (as_seq bufi h0)))) ->
		buf:lbuffer a (nb * bs) ->
		Stack unit
		                  (requires (fun h -> h == h0 /\ live h buf))
				  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 buf h0 h1 /\
							as_seq buf h1 == LSeq.map_blocks #a bs nb (f_spec h0) (as_seq buf h0)))
*)
inline_for_extraction
val reduce_blocks: #h0:mem ->
		#a:Type0 ->
		#r:Type0 ->
		#bs:size_nat{bs > 0} ->
		#nb:size_nat{nb * bs <= maxint SIZE} ->
		#rlen:size_nat ->
		blocksize:size_t{size_v blocksize == bs} ->
		nblocks:size_t{size_v nblocks == nb} ->
		rbuf: lbuffer r rlen ->
		f_spec:(mem -> i:size_nat{i + 1 <= nb} -> LSeq.lseq a bs -> LSeq.lseq r (rlen) -> LSeq.lseq r (rlen)) ->
		f:(i:size_t{size_v i + 1 <= nb} -> bufi:lbuffer a bs -> Stack unit
				  (requires (fun h -> live h bufi /\ live h rbuf /\ disjoint bufi rbuf /\ disjoint rbuf bufi /\
						   preserves_live h0 h /\
				                   modifies1 rbuf h0 h))
				  (ensures (fun h _ h' ->
						   preserves_live h h' /\
						   modifies1 rbuf h h' /\
						   as_seq rbuf h' ==
							  f_spec h0 (size_v i) (as_seq bufi h0) (as_seq rbuf h)))) ->
		buf:lbuffer a (nb * bs) ->
		Stack unit
		                  (requires (fun h -> h == h0 /\ live h buf /\ live h rbuf))
				  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 rbuf h0 h1 /\
							as_seq rbuf h1 == LSeq.reduce_blocks #a #(LSeq.lseq r (rlen)) (bs) (nb) (f_spec h0) (as_seq buf h0) (as_seq rbuf h0)))



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
	    start:size_t -> fin:size_t{v start <= v fin} -> spec:(i:size_t{v start <= i /\ i < v fin} -> a -> Tot a) ->
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
	    n:size_t -> spec:(i:size_t{i < v n} -> a -> Tot a) ->
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
