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

inline_for_extraction val index: #a:Type0 -> #len:size_nat -> b:lbuffer a (len) -> i:size_t{v i < len} ->
  Stack a
    (requires (fun h0 -> live h0 b))
	 (ensures (fun h0 r h1 -> h0 == h1 /\ r == LSeq.index #a #(len) (as_lseq #a #len b h0) (v i)))

inline_for_extraction val upd: #a:Type0 -> #len:size_nat -> b:lbuffer a (len) -> i:size_t{v i < len} -> x:a ->
  Stack unit
	 (requires (fun h0 -> live h0 b /\ len > 0))
	 (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ modifies1 b h0 h1
		                  /\ as_lseq #a #len b h1 == LSeq.upd #a #(len) (as_lseq #a #len b h0) (v i) x))

inline_for_extraction let op_Array_Assignment #a #len = upd #a #len
inline_for_extraction let op_Array_Access #a #len = index #a #len


inline_for_extraction val create: #a:Type0 -> #len:size_nat -> clen:size_t{v clen == len} -> init:a ->
  StackInline (lbuffer a len)
    (requires (fun h0 -> True))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
					           creates1 r h0 h1 /\
					           modifies1 r h0 h1 /\
					           as_lseq #a #len r h1 == LSeq.create #a len init))

inline_for_extraction val createL: #a:Type0 -> init:list a{List.Tot.length init <= max_size_t} ->
  StackInline (lbuffer a (List.Tot.length init))
    (requires (fun h0 -> True))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ creates1 r h0 h1
				            /\ modifies1 r h0 h1
					         /\ as_lseq r h1 == LSeq.createL #a init))

// FIXME : UNSOUND EXPERIMENT
inline_for_extraction val alloc: #a:Type0 -> #b:Type0 -> #len:size_nat -> clen:size_t{v clen == len} -> init:a ->
  reads:list bufitem ->
  writes:list bufitem ->
  spec:(h0:mem -> r:b -> h1:mem -> Type) ->
  impl:(buf:lbuffer a len -> Stack b
    (requires (fun h -> live h buf /\ as_lseq buf h == LSeq.create #a len init /\ live_list h reads /\ live_list h writes /\ disjoint_list buf reads /\ disjoint_list buf writes))
	 (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
				              modifies (BufItem buf :: writes) h0 h1 /\
						        spec h0 r h1))) ->
  Stack b
    (requires (fun h0 -> live_list h0 reads /\ live_list h0 writes))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
					           modifies writes h0 h1 /\
					           spec h0 r h1))


inline_for_extraction val alloc1: #h0:mem -> #a:Type0 -> #b:Type0 -> #w:Type0 -> #len:size_nat -> #wlen:size_nat -> clen:size_t{v clen == len} -> init:a ->
  write:lbuffer w wlen ->
  spec:(h:mem -> GTot(r:b -> LSeq.lseq w wlen -> Type)) ->
  impl:(buf:lbuffer a len -> Stack b
    (requires (fun h -> creates1 #a #len buf h0 h /\
		     preserves_live h0 h /\
		     modifies1 buf h0 h /\
		     as_lseq buf h == LSeq.create #a len init /\
		     live h0 write))
    (ensures (fun h r h' -> preserves_live h h' /\ modifies2 buf write h h' /\
			 spec h0 r (as_lseq write h')))) ->
  Stack b
    (requires (fun h -> h == h0 /\ live h write))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
		          modifies1 write h0 h1 /\
		          spec h0 r (as_lseq write h1)))


inline_for_extraction val alloc1_with: #h0:mem -> #a:Type0 -> #b:Type0 -> #w:Type0 -> #len:size_nat -> #wlen:size_nat -> clen:size_t{v clen == len} ->
  init_spec: LSeq.lseq a len ->
  init:(unit -> StackInline (lbuffer a len)
               (requires (fun h -> h == h0))
               (ensures  (fun h0 r h1 -> creates1 #a #len r h0 h1 /\
		                                preserves_live h0 h1 /\
		                                modifies1 r h0 h1 /\
		                                as_lseq r h1 == init_spec))) ->
  write:lbuffer w wlen ->
  spec:(h:mem -> GTot(r:b -> LSeq.lseq w wlen -> Type)) ->
  impl:(buf:lbuffer a len -> Stack b
    (requires (fun h -> creates1 #a #len buf h0 h /\
		     preserves_live h0 h /\
		     modifies1 buf h0 h /\
		     as_lseq buf h == init_spec /\
		     live h0 write))
    (ensures (fun h r h' -> preserves_live h h' /\ modifies2 buf write h h' /\
			 spec h0 r (as_lseq write h')))) ->
  Stack b
    (requires (fun h -> h == h0 /\ live h write))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
		          modifies1 write h0 h1 /\
		          spec h0 r (as_lseq write h1)))

(** This allocation function creates one buffer and writes two buffers.
    It reasons about the output of the first written buffer but not about
    the second one, for which functionnal correctness is ignored. *)
inline_for_extraction val alloc_modifies2:
    #h0:mem
  -> #a:Type0
  -> #b:Type0
  -> #w0:Type0
  -> #w1:Type0
  -> #len:size_nat
  -> #wlen0:size_nat
  -> #wlen1:size_nat
  -> clen:size_t{v clen == len}
  -> init:a
  -> write0:lbuffer w0 wlen0
  -> write1:lbuffer w1 wlen1
  -> spec:(h:mem -> GTot(r:b -> LSeq.lseq w0 wlen0 -> Type))
  -> impl:(buf:lbuffer a len -> Stack b
    (requires (fun h -> creates1 #a #len buf h0 h
		             /\ live h0 write0 /\ live h0 write1
                   /\ preserves_live h0 h
		             /\ modifies1 buf h0 h
		             /\ as_lseq buf h == LSeq.create #a len init))
    (ensures (fun h r h' -> preserves_live h h' /\ modifies3 buf write0 write1 h h'
                       /\ spec h0 r (as_lseq write0 h')))) ->
  Stack b
    (requires (fun h -> h == h0 /\ live h write0 /\ live h write1))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
		                    modifies2 write0 write1 h0 h1 /\
		                    spec h0 r (as_lseq write0 h1)))


(* Various Allocation Patterns *)

val map: #a:Type -> #len:size_nat -> clen:size_t{v clen == len} -> f:(a -> Tot a) -> b:lbuffer a (len) ->
  Stack unit
    (requires (fun h0 -> live h0 b))
	 (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 b h0 h1
				            /\ as_lseq #a #len b h1 == LSeq.map #a #a #(len) f (as_lseq #a #len b h0)))

inline_for_extraction
val map2: #a1:Type -> #a2:Type -> #len:size_nat -> clen:size_t{v clen == len} -> f:(a1 -> a2 -> Tot a1) -> b1:lbuffer a1 len -> b2:lbuffer a2 len ->
  Stack unit
	 (requires (fun h0 -> live h0 b1 /\ live h0 b2))
	 (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 b1 h0 h1
                        /\ as_lseq #a1 #len b1 h1 == LSeq.map2 #a1 #a2 #a1 #len f (as_lseq #a1 #len b1 h0) (as_lseq #a2 #len b2 h0)))

inline_for_extraction
val copy: #a:Type -> #len:size_nat -> o:lbuffer a len -> clen:size_t{v clen == len} -> i:lbuffer a len ->
  Stack unit
    (requires (fun h0 -> live h0 i /\ live h0 o ))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
                          modifies1 o h0 h1 /\
                          as_lseq o h1 == as_lseq i h0))


(* Integer Parsing and Serialization *)

inline_for_extraction
val uint_from_bytes_le:
  #t:m_inttype ->
  i:lbuffer uint8 (numbytes t) ->
  Stack (uint_t t)
	(requires (fun h0 -> live h0 i))
	(ensures (fun h0 o h1 -> preserves_live h0 h1 /\
			      o == LSeq.uint_from_bytes_le #t (as_lseq i h0)))

inline_for_extraction
val uint_from_bytes_be:
  #t:m_inttype ->
  i:lbuffer uint8 (numbytes t) ->
  Stack (uint_t t)
	(requires (fun h0 -> live h0 i))
	(ensures (fun h0 o h1 -> preserves_live h0 h1 /\
			      o == LSeq.uint_from_bytes_be #t (as_lseq i h0)))

inline_for_extraction
val uint_to_bytes_le:
  #t:m_inttype ->
  o:lbuffer uint8 (numbytes t) ->
  i:uint_t t ->
  Stack unit
	(requires (fun h0 -> live h0 o))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 == LSeq.uint_to_bytes_le #t i))
inline_for_extraction
val uint_to_bytes_be:
  #t:m_inttype ->
  o:lbuffer uint8 (numbytes t) ->
  i:uint_t t ->
  Stack unit
	(requires (fun h0 -> live h0 o))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 == LSeq.uint_to_bytes_be #t i))

(* EXPERIMENTAL: Various Allocation Patterns *)

inline_for_extraction let palloc #a #b #len clen init reads writes spec impl = alloc #a #b #len clen init reads writes spec impl

let salloc_inv (h0:mem) (h1:mem) (#a:Type) (#b:Type0) (len:size_nat)  (buf:lbuffer a len) (init:a) (reads:list bufitem) (writes:list bufitem)
  (spec:(h:mem -> b -> mem -> Type)) : Type =
  live h0 buf /\ live_list h0 reads /\ live_list h0 writes
  /\ preserves_live h0 h1
  /\ disjoint_list buf reads /\ disjoint_list buf writes

    (* (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ creates1 r h0 h1 *)
	 (*   		            /\ modifies1 r h0 h1 *)
	 (*   			         /\ as_lseq r h1 == LSeq.createL #a init)) *)

inline_for_extraction val salloc:
  #h0:mem -> #a:Type0 -> #b:Type0 -> #len:size_nat ->
  clen:size_t{v clen == len} ->
  init:a ->
  reads:list bufitem ->
  writes:list bufitem ->
  spec:(h0:mem -> r:b -> h1:mem -> Type) ->
  impl:(buf:lbuffer a len -> Stack b
    (requires (fun h -> preserves_live h0 h /\ creates1 buf h0 h /\ modifies1 buf h0 h /\ as_lseq buf h == LSeq.create len init))// prsalloc_inv h0 h #a len buf init reads writes spec /\ as_lseq #a #len buf h == LSeq.create #a len init))
	 (ensures (fun h00 r h11 -> preserves_live h00 h11 ///\ modifies1 h00 h11 /\ as_lseq buf h1 == LSeq.create len init //salloc_inv h0 h1 #a len buf init reads writes spec
				              /\ modifies (BufItem buf :: writes) h00 h11
						        /\ spec h00 r h11))) ->
  Stack b
    (requires (fun h -> live_list h0 reads /\ live_list h0 writes /\ disjoint_lists reads writes))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
					           modifies writes h0 h1 /\
					           spec h0 r h1))


inline_for_extraction val salloc11:
  #h0:mem -> #a:Type0 -> #b:Type0 -> #w:Type0 -> #len:size_nat -> #wlen:size_nat ->
  clen:size_t{v clen == len} ->
  init:a ->
  reads:list bufitem ->
  write:lbuffer w wlen ->
  spec:(h0:mem -> r:b -> h1:LSeq.lseq w wlen -> Type) ->
  impl:(buf:lbuffer a len -> Stack b
    (requires (fun h -> preserves_live h0 h /\ creates1 buf h0 h /\ modifies1 buf h0 h /\ as_lseq buf h == LSeq.create len init))
	 (ensures (fun h00 r h11 -> preserves_live h00 h11
				              /\ modifies2 buf write  h00 h11
						        /\ spec h0 r (as_lseq write h11)))) ->
  Stack b
    (requires (fun h -> live_list h0 reads /\ live h0 write /\ disjoint_list write reads))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
					           modifies1 write h0 h1 /\
					           spec h0 r (as_lseq write h1)))


inline_for_extraction val salloc21:
  #h0:mem -> #b:Type0 -> #a0:Type0 -> #a1:Type0 -> #w:Type0 -> #len0:size_nat -> #len1:size_nat -> #wlen:size_nat ->
  clen0:size_t{v clen0 == len0} ->
  clen1:size_t{v clen1 == len1} ->
  init0:a0 ->
  init1:a1 ->
  reads:list bufitem ->
  write:lbuffer w wlen ->
  spec:(mem -> b -> LSeq.lseq w wlen -> Type) ->
  impl:(buf0:lbuffer a0 len0 -> buf1:lbuffer a1 len1 -> Stack b
    (requires (fun h -> preserves_live h0 h /\ creates2 buf0 buf1 h0 h /\ modifies2 buf0 buf1 h0 h
                   /\ as_lseq buf0 h == LSeq.create #a0 len0 init0
                   /\ as_lseq buf1 h == LSeq.create #a1 len1 init1))
	 (ensures (fun h00 r h11 -> preserves_live h00 h11
				              /\ modifies3 buf0 buf1 write h00 h11
						        /\ spec h0 r (as_lseq write h11)))) ->
  Stack b
    (requires (fun h -> live_list h0 reads /\ live h0 write /\ disjoint_list write reads))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
					           modifies1 write h0 h1 /\
					           spec h0 r (as_lseq write h1)))



(* EXPERIMENTAL: Various Looping Patterns *)

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
val iteri: #a:Type -> #len:size_nat -> n:size_t ->
  spec:(i:size_nat{i < v n}  -> LSeq.lseq a (len) -> Tot (LSeq.lseq a (len))) ->
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
val iter: #a:Type -> #len:size_nat -> n:size_t ->
  spec:(LSeq.lseq a (len) -> LSeq.lseq a (len)) ->
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


let loop_inv (h0:mem) (h1:mem) (#a:Type) (len:size_nat) (n:size_nat)  (buf:lbuffer a len)
  (spec:(h:mem -> GTot (i:size_nat{i < n} -> LSeq.lseq a len -> Tot (LSeq.lseq a len)))) (i:size_nat{i <= n}) : Type =
  live h0 buf /\ preserves_live h0 h1
  /\ modifies1 buf h0 h1
  /\ (let b0 = as_lseq #a #len buf h0 in
    let b1 = as_lseq #a #len buf h1 in
    b1 == LSeq.repeati #(LSeq.lseq a len) i (spec h0) b0)

inline_for_extraction
val loop:
  #h0:mem ->
  #a:Type0 ->
  #len:size_nat ->
  n:size_t ->
  buf:lbuffer a len ->
  spec:(h:mem -> GTot (i:size_nat{i < v n} -> LSeq.lseq a len -> Tot (LSeq.lseq a len))) ->
  impl:(i:size_t{v i < v n} -> Stack unit
    (requires (fun h -> loop_inv h0 h #a len (v n) buf spec (v i)))
	 (ensures (fun _ _ h1 -> loop_inv h0 h1 #a len (v n) buf spec (v i + 1)))) ->
  Stack unit
	 (requires (fun h -> live h buf /\ h0 == h))
	 (ensures (fun _ _ h1 -> preserves_live h0 h1
                       /\ modifies1 buf h0 h1
                       /\ (let b0 = as_lseq #a #len buf h0 in
                       let b1 = as_lseq #a #len buf h1 in
                       b1 == LSeq.repeati #(LSeq.lseq a len) (v n) (spec h0) b0)))


let loop2_inv (h0:mem) (h1:mem) (#a0:Type) (#a1:Type) (len0:size_nat) (len1:size_nat) (n:size_nat)  (buf0:lbuffer a0 len0) (buf1:lbuffer a1 len1)
  (spec:(h:mem -> GTot (i:size_nat{i < n} -> LSeq.lseq a0 len0 -> Tot (LSeq.lseq a0 len0)))) (i:size_nat{i <= n}) : Type =
  live h0 buf0 /\ live h0 buf1 /\ preserves_live h0 h1
  /\ modifies2 buf0 buf1 h0 h1
  /\ (let b0 = as_lseq #a0 #len0 buf0 h0 in
    let b1 = as_lseq #a0 #len0 buf0 h1 in
    b1 == LSeq.repeati #(LSeq.lseq a0 len0) i (spec h0) b0)

inline_for_extraction
val loop2:
  #h0:mem ->
  #a0:Type0 ->
  #a1:Type0 ->
  #len0:size_nat ->
  #len1:size_nat ->
  n:size_t ->
  buf0:lbuffer a0 len0 ->
  buf1:lbuffer a1 len1 ->
  spec:(h:mem -> GTot (i:size_nat{i < v n} -> LSeq.lseq a0 len0 -> Tot (LSeq.lseq a0 len0))) ->
  impl:(i:size_t{v i < v n} -> Stack unit
    (requires (fun h -> loop2_inv h0 h #a0 #a1 len0 len1 (v n) buf0 buf1 spec (v i)))
	 (ensures (fun _ _ h1 -> loop2_inv h0 h1 #a0 #a1 len0 len1 (v n) buf0 buf1 spec (v i + 1)))) ->
  Stack unit
	 (requires (fun h -> live h buf0 /\ live h buf1 /\ h0 == h))
	 (ensures (fun _ _ h1 -> preserves_live h0 h1
                       /\ modifies2 buf0 buf1 h0 h1
                       /\ (let b0 = as_lseq #a0 #len0 buf0 h0 in
                       let b1 = as_lseq #a0 #len0 buf0 h1 in
                       b1 == LSeq.repeati #(LSeq.lseq a0 len0) (v n) (spec h0) b0)))


#reset-options "--z3rlimit 1000 --max_fuel 0"
open FStar.Mul

inline_for_extraction
val map_blocks: #h0:mem ->
		#a:Type0 ->
		#bs:size_nat{bs > 0} ->
		#nb:size_nat{nb * bs <= maxint SIZE} ->
		blocksize:size_t{size_v blocksize == bs} ->
		nblocks:size_t{size_v nblocks == nb} ->
		buf:lbuffer a (nb * bs) ->
		f_spec:(mem -> GTot (i:size_nat{i + 1 <= nb} -> LSeq.lseq a bs -> LSeq.lseq a bs)) ->
		f:(i:size_t{size_v i + 1 <= nb} -> Stack unit
				  (requires (fun h -> live h buf /\
						   preserves_live h0 h /\
				                   modifies1 buf h0 h))
				  (ensures (fun h _ h' ->
						   preserves_live h h' /\
						  (let bufi = sub buf (i *. blocksize) blocksize in
						   modifies1 bufi h h' /\
						   as_lseq bufi h' ==
						   f_spec h (size_v i) (as_lseq bufi h))))) ->
		Stack unit
		                  (requires (fun h -> h == h0 /\ live h buf))
				  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 buf h0 h1 /\
							as_lseq buf h1 == LSeq.map_blocks #a bs nb (f_spec h0) (as_lseq buf h0)))

(*
val map_blocks: #h0:mem ->
		#a:Type0 ->
		#bs:size_nat{bs > 0} ->
		#nb:size_nat{nb * bs <= maxint SIZE} ->
		blocksize:size_t{size_v blocksize == bs} ->
		nblocks:size_t{size_v nblocks == nb} ->
		f_spec:(mem -> GTot (i:size_nat{i + 1 <= nb} -> LSeq.lseq a bs -> LSeq.lseq a bs)) ->
		f:(i:size_t{size_v i + 1 <= nb} -> bufi:lbuffer a bs -> Stack unit
				  (requires (fun h -> live h bufi /\
						   preserves_live h0 h /\
				                   modifies1 bufi h0 h))
				  (ensures (fun h _ h' ->
						   preserves_live h h' /\
						   modifies1 bufi h h' /\
						   as_lseq bufi h' ==
						   f_spec h0 (size_v i) (as_lseq bufi h0)))) ->
		buf:lbuffer a (nb * bs) ->
		Stack unit
		                  (requires (fun h -> h == h0 /\ live h buf))
				  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 buf h0 h1 /\
							as_lseq buf h1 == LSeq.map_blocks #a bs nb (f_spec h0) (as_lseq buf h0)))
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
		f_spec:(mem -> i:size_nat{i + 1 <= nb} -> LSeq.lseq a bs -> LSeq.lseq r rlen -> LSeq.lseq r rlen) ->
		f:(i:size_t{size_v i + 1 <= nb} -> bufi:lbuffer a bs -> Stack unit
				  (requires (fun h -> live h bufi /\ live h rbuf /\ disjoint bufi rbuf /\ disjoint rbuf bufi /\
						   preserves_live h0 h /\
				                   modifies1 rbuf h0 h))
				  (ensures (fun h _ h' ->
						   preserves_live h h' /\
						   modifies1 rbuf h h' /\
						   as_lseq rbuf h' ==
							  f_spec h0 (size_v i) (as_lseq bufi h0) (as_lseq rbuf h)))) ->
		buf:lbuffer a (nb * bs) ->
		Stack unit
		                  (requires (fun h -> h == h0 /\ live h buf /\ live h rbuf))
				  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 rbuf h0 h1 /\
							as_lseq rbuf h1 == LSeq.reduce_blocks #a #(LSeq.lseq r rlen) bs nb (f_spec h0) (as_lseq buf h0) (as_lseq rbuf h0)))



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

// let loop_inv' (h0:mem) (h1:mem) (#a:Type) (len:size_nat) (n:size_nat)  (buf:lbuffer a len)
//   (spec:(h:mem -> i:size_nat{i < n} -> LSeq.lseq a len -> GTot (LSeq.lseq a len))) (i:size_nat{i <= n}) : Type =
//   preserves_live h0 h1
//   /\ modifies1 buf h0 h1
//   /\ (let b0 = as_lseq #a #len buf h0 in
//     let b1 = as_lseq #a #len buf h1 in
//     b1 == LSeq.repeati_ghost #(LSeq.lseq a len) i (spec h0) b0)

// inline_for_extraction
// val loop':
//   #a:Type0 ->
//   #len:size_nat ->
//   h0:mem ->
//   n:size_t ->
//   buf:lbuffer a len ->
//   spec:(h:mem -> i:size_nat{i < v n} -> LSeq.lseq a len -> GTot (LSeq.lseq a len)) ->
//   impl:(i:size_t{v i < v n} -> Stack unit
//     (requires (fun h -> loop_inv h0 h #a len (v n) buf spec (v i)))
// 	 (ensures (fun _ _ h1 -> loop_inv h0 h1 #a len (v n) buf spec (v i + 1)))) ->
//   Stack unit
// 	 (requires (fun h -> live h buf))
// 	 (ensures (fun _ _ h1 -> preserves_live h0 h1
//                        /\ modifies1 buf h0 h1
//                        /\ (let b0 = as_lseq #a #len buf h0 in
//                        let b1 = as_lseq #a #len buf h1 in
//                        b1 == LSeq.repeati_ghost #(LSeq.lseq a len) (v n) (spec h0) b0)))

*)
