module Lib.Buffer

open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.RawIntTypes

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module LMB = LowStar.Monotonic.Buffer

module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

module Seq = Lib.Sequence
module ByteSeq = Lib.ByteSequence
module Loop = Lib.LoopCombinators

#set-options "--z3rlimit 15"

inline_for_extraction noextract
let v = size_v

type buftype = 
  | MUT
  | IMMUT

unfold let buffer_t (ty:buftype) (a:Type0) =
  match ty with
  | IMMUT -> IB.ibuffer a
  | MUT -> B.buffer a
  
(** Definition of a mutable Buffer *)
unfold let buffer (a:Type0) = buffer_t MUT a

(** Definition of an immutable Buffer *)
unfold let ibuffer (a:Type0) = buffer_t IMMUT a

(** Length of buffers *)
let length (#t:buftype) (#a:Type0) (b:buffer_t t a) = 
  match t with
  | MUT-> B.length (b <: buffer a)
  | IMMUT -> IB.length (b <: ibuffer a)
  
let lbuffer_t (ty:buftype) (a:Type0) (len:size_t) =
  b:buffer_t ty a{length #ty #a b == v len}

let lbuffer (a:Type0) (len:size_t) = lbuffer_t MUT a len
let ilbuffer (a:Type0) (len:size_t) = lbuffer_t IMMUT a len

(** Liveness of buffers *)
let live (#t:buftype) (#a:Type0) (h:HS.mem) (b:buffer_t t a) : Type = 
  match t with
  | MUT -> B.live h (b <: buffer a)
  | IMMUT -> IB.live h (b <: ibuffer a)
//val live: #t:buftype -> #a:Type0 -> h:HS.mem -> b:buffer_t t a -> Type

let loc (#t:buftype) (#a:Type0) (b:buffer_t t a) : GTot B.loc = 
  match t with
  | MUT -> B.loc_buffer (b <: buffer a)
  | IMMUT -> B.loc_buffer (b <: ibuffer a) 

let union (l1:B.loc) (l2:B.loc) : GTot B.loc = B.loc_union l1 l2
let ( |+| ) (l1:B.loc) (l2:B.loc) : GTot B.loc = union l1 l2

(** Generalized modification clause for Buffer locations *)
let modifies
  (s: B.loc)
  (h1 h2: HS.mem):
  GTot Type0 = B.modifies s h1 h2 /\ ST.equal_domains h1 h2
//val modifies: s:B.loc -> h1:HS.mem -> h2:HS.mem -> GTot Type0

val modifies_preserves_live: #t:buftype -> #a:Type0 -> b:buffer_t t a -> l:B.loc ->
			     h0:mem -> h1:mem -> Lemma
			     (requires (modifies l h0 h1 /\ live h0 b))
			     (ensures (live h1 b))
			     [SMTPatOr [[SMTPat (modifies l h0 h1); SMTPat (live h0 b)];
			                [SMTPat (modifies l h0 h1); SMTPat (live h1 b)]]]

val modifies_includes: l1:B.loc -> l2:B.loc -> h0:mem -> h1:mem -> Lemma
		     (requires (modifies l1 h0 h1 /\ B.loc_includes l2 l1))
		     (ensures (modifies l2 h0 h1))

val modifies_trans: l1:B.loc ->  l2:B.loc -> h0:mem -> h1:mem -> h2:mem -> Lemma
		     (requires (modifies l1 h0 h1 /\ modifies l2 h1 h2))
		     (ensures (modifies (l1 |+| l2) h0 h2))



(** Disjointness clause for Buffers *)
let disjoint
  (#t1 #t2:buftype)
  (#a1 #a2:Type0)
  (b1:buffer_t t1 a1)
  (b2:buffer_t t2 a2)
  : GTot Type0 = 
    B.loc_disjoint (loc b1) (loc b2)

(** Modification for no Buffer *)
let modifies0 (h1 h2: HS.mem) : GTot Type0 = modifies (B.loc_none) h1 h2

(** Modification clause for one Buffer *)
let modifies1
  (#a:Type0)
  (#len:size_t)
  (b: lbuffer a len)
  (h1 h2: HS.mem):
  GTot Type0 = modifies (loc  b) h1 h2

(** Modification clause for two Buffers *)
let modifies2
  (#a0:Type0)
  (#a1:Type0)
  (#len0:size_t)
  (#len1:size_t)
  (b0: lbuffer a0 len0)
  (b1: lbuffer a1 len1)
  (h1 h2: HS.mem):
  GTot Type0 = modifies (loc b0 |+| loc  b1) h1 h2

(** Modification clause for three Buffers *)
let modifies3
  (#a0:Type0)
  (#a1:Type0)
  (#a2:Type0)
  (#len0:size_t)
  (#len1:size_t)
  (#len2:size_t)
  (b0: lbuffer a0 len0)
  (b1: lbuffer a1 len1)
  (b2: lbuffer a1 len1)
  (h1 h2: HS.mem):
  GTot Type0 = modifies (loc b0 |+| loc b1 |+| loc b2) h1 h2

(** Ghost reveal a Buffer as its Pure Sequence *)
let as_seq
  (#t:buftype)
  (#a:Type0)
  (#len:size_t)
  (h:HS.mem)
  (b:lbuffer_t t a len):
  GTot (Seq.lseq a (v len)) = 
  match t with
  | MUT -> B.as_seq h (b <: buffer a)
  | IMMUT -> IB.as_seq h (b <: ibuffer a)

#reset-options "--z3rlimit 100"
(** Ghost view of a subset of a mutable Buffer *)
let gsub
  (#t:buftype)
  (#a:Type0)
  (#len:size_t)
  (b:lbuffer_t t a len)
  (start:size_t)
  (n:size_t{v start + v n <= v len}) : GTot (lbuffer_t t a n)= 
  match t with
  | IMMUT-> 
    let b = IB.igsub (b <: ibuffer a) start n in
    assert (B.length b == v n);
    (b <: ilbuffer a n)
  | MUT -> 
    let b = B.gsub (b <: buffer a) start n in
    assert (B.length b == v n);
    (b <: lbuffer a n)

val live_sub: #t:buftype -> #a:Type0 -> #len:size_t -> b:lbuffer_t t a len -> 
			start:size_t -> n:size_t{v start + v n <= v len} ->
			h:mem -> Lemma
			     (ensures (live h b <==> live h (gsub b start n)))
			     [SMTPat (live h (gsub b start n))]

val modifies_sub: #t:buftype -> #a:Type0 -> #len:size_t -> b:lbuffer_t t a len -> 
			start:size_t -> n:size_t{v start + v n <= v len} ->
			h0:mem -> h1:mem -> Lemma
			     (requires (modifies (loc (gsub b start n)) h0 h1))
			     (ensures (modifies (loc b) h0 h1))
			     [SMTPat (modifies (loc (gsub b start n)) h0 h1)]

inline_for_extraction
val as_seq_gsub:
    #t:buftype
  -> #a:Type0
  -> #len:size_t
  -> h:HS.mem
  -> b:lbuffer_t t a len
  -> start:size_t
  -> n:size_t{v start + v n <= v len} ->
  Lemma
   (as_seq h (gsub b start n) ==
    Seq.sub #a #(v len) (as_seq h b) (v start) (v n))
  [SMTPat (Seq.sub #a #(v len) (as_seq h b) (v start) (v n))]

(** Subset of a mutable Buffer *)
inline_for_extraction
val sub:
    #t:buftype
  -> #a:Type0
  -> #len:size_t
  -> b:lbuffer_t t a len
  -> start:size_t
  -> n:size_t{v start + v n <= v len} ->
  Stack (lbuffer_t t a n)
    (requires fun h0 -> live h0 b)
    (ensures  fun h0 r h1 -> h0 == h1 /\ live h1 r /\ r == gsub b start n)

(** Access a specific value in an mutable Buffer *)
inline_for_extraction
val index:
    #t:buftype
  -> #a:Type0
  -> #len:size_t{v len > 0}
  -> b:lbuffer_t t a len
  -> i:size_t{v i < v len} ->
  Stack a
    (requires fun h0 -> live h0 b)
    (ensures  fun h0 r h1 -> h0 == h1 /\
      r == Seq.index #a #(v len) (as_seq h1 b) (v i))

(** Update a specific value in a mutable Buffer *)
inline_for_extraction
val upd:
    #a:Type0
  -> #len:size_t{v len > 0}
  -> b:lbuffer a len
  -> i:size_t{v i < v len}
  -> x:a ->
  Stack unit
    (requires fun h0 -> live h0 b)
    (ensures  fun h0 _ h1 ->
      modifies (loc  b) h0 h1 /\ 
      as_seq h1 b == Seq.upd #a #(v len) (as_seq h0 b) (v i) x)

(** Operator definition to update a mutable Buffer *)
inline_for_extraction
let op_Array_Assignment #a #len = upd #a #len

(** Operator definition to access a mutable Buffer *)
inline_for_extraction
let op_Array_Access #t #a #len = index #t #a #len

(** Access to the pure sequence-based value associated to an index of a mutable Buffer  *)
(* We don't have access to Lib.Sequence.fst
   to get the fact `Lib.Sequence.index == FStar.Seq.index` *)
let bget (#t:buftype) (#a:Type0) (#len:size_t) (h:mem) 
	 (b:lbuffer_t t a len) (i:size_nat{i < v len}) 
	 : GTot a =
    match t with
    | MUT -> B.get h (b <: buffer a) i
    | IMMUT -> IB.get h (b <: ibuffer a) i

val bget_as_seq:#t:buftype -> #a:Type0 -> #len:size_t -> h:mem ->
	 b:lbuffer_t t a len -> i:size_nat -> Lemma 
	   (requires (i < v len))
	   (ensures (bget #t #a #len h b i == Seq.index #a #(v len) (as_seq h b) i))
	   [SMTPat (bget #t #a #len h b i)]

(** Allocate a fixed-length mutable Buffer and initialize it to value [init] *)

let stack_allocated (#a:Type0) (#len:size_t) (b:lbuffer a len) 
		    (h0:mem) (h1:mem) (s:Seq.lseq a (v len)) = 
    let b: B.buffer a = b in 
    B.alloc_post_mem_common b h0 h1 s /\
    B.frameOf b = HS.get_tip h0

let global_allocated (#a:Type0) (#len:size_t) (b:ilbuffer a len) 
		    (h0:mem) (h1:mem) (s:Seq.lseq a (v len)) = 
    let b: ibuffer a = b in 
    B.frameOf b == HyperStack.root /\ 
    B.alloc_post_mem_common b h0 h1 s 

let recallable (#t:buftype) (#a:Type0) (#len:size_t) (b:lbuffer_t t a len) =
    match t with
    | IMMUT ->  B.recallable (b <: ibuffer a)
    | MUT -> B.recallable (b <: buffer a)


unfold private let cpred (#a:Type0) (s:Seq.seq a) : B.spred a = fun s1 -> FStar.Seq.equal s s1
let witnessed (#a:Type0) (#len:size_t) (b:ilbuffer a len) (s:Seq.lseq a (v len)) = 
    B.witnessed (b <: ibuffer a) (cpred s)  

inline_for_extraction
val create:
    #a:Type0
  -> len:size_t
  -> init:a ->
  StackInline (lbuffer a len)
    (requires fun h0 -> v len > 0)
    (ensures  fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 (Seq.create (v len) init))

      
(** Allocate a fixed-length mutable Buffer based on an existing List *)
inline_for_extraction noextract
val createL:
    #a:Type0
  -> init:list a{List.Tot.length init <= max_size_t} ->
  StackInline (lbuffer a (size (normalize_term (List.Tot.length init))))
    (requires fun h0 -> B.alloca_of_list_pre #a init)
    (ensures fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 (Seq.of_list init))


(** Allocate a top-level fixed-length immutable Buffer and initialize it to value [init] *)
inline_for_extraction noextract
val createL_global:
    #a:Type0
  -> init:list a{normalize (List.Tot.length init <= max_size_t)} ->
  ST (b:ilbuffer a (size (normalize_term (List.Tot.length init))))
    (requires fun h0 -> B.gcmalloc_of_list_pre #a HyperStack.root init)
    (ensures  fun h0 b h1 -> global_allocated b h0 h1 (Seq.of_list init) /\ 
                          recallable b /\
			  witnessed b (Seq.of_list init))

(** Recall the liveness and content of a global immutable Buffer *)
inline_for_extraction noextract
val recall_contents:
    #a:Type0
  -> #len:size_t{v len <= max_size_t}
  -> b:ilbuffer a len
  -> s:Seq.lseq a (v len) ->
  ST unit
    (requires fun h0 -> (live h0 b \/ recallable b) /\ witnessed b s)
    (ensures  fun h0 _ h1 -> h0 == h1 /\ live h0 b /\ as_seq h0 b == s)

(** Copy a mutable Buffer in another mutable Buffer *)
inline_for_extraction
val copy:
    #t:buftype
  -> #a:Type
  -> #len:size_t
  -> o:lbuffer a len
  -> i:lbuffer_t t a len ->
  Stack unit
    (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint i o)
    (ensures  fun h0 _ h1 ->
      modifies (loc  o) h0 h1 /\
      as_seq h1 o == as_seq h0 i)

(**
* Set all elements of a mutable buffer to a specific value
*
* WARNING: don't rely on the extracted implementation for secure erasure,
* C compilers may remove optimize it away.
*)
inline_for_extraction
val memset:
    #a:Type
  -> #blen:size_t
  -> b:lbuffer a blen
  -> w:a
  -> len:size_t{v len <= v blen} ->
  Stack unit
    (requires fun h0 -> live h0 b)
    (ensures  fun h0 _ h1 ->
      modifies1 b h0 h1 /\
      as_seq h1 (gsub b 0ul len) == Seq.create (v len) w /\
      as_seq h1 (gsub b len (blen -! len)) ==
      as_seq h0 (gsub b len (blen -! len)))

(** Copy a mutable Buffer in a part of another mutable Buffer *)
inline_for_extraction
val update_sub:
    #t:buftype
  -> #a:Type
  -> #len:size_t
  -> dst:lbuffer a len
  -> start:size_t
  -> n:size_t{v start + v n <= v len}
  -> src:lbuffer_t t a n ->
  Stack unit
    (requires fun h -> live h dst /\ live h src /\ disjoint dst src)
    (ensures  fun h0 _ h1 -> modifies (loc  dst) h0 h1 /\
      as_seq h1 dst == Seq.update_sub (as_seq h0 dst) (v start) (v n) (as_seq h0 src))


(** Update a part of a mutable Buffer in-place with the application of a function F on another Buffer *)
inline_for_extraction
val update_sub_f:
    #a:Type
  -> #len:size_t
  -> h0:mem
  -> buf:lbuffer a len
  -> start:size_t
  -> n:size_t{v start + v n <= v len}
  -> spec:(mem -> GTot (Seq.lseq a (v n)))
  -> f:(b:lbuffer a n -> Stack unit
      (requires fun h -> h0 == h /\ 
		      live h b)
      (ensures  fun h0 _ h1 ->
             modifies (loc  b) h0 h1 /\
             as_seq h1 b == spec h0)) ->
  Stack unit
    (requires fun h -> h0 == h /\ live h buf)
    (ensures  fun h0 _ h1 -> modifies (loc  buf) h0 h1 /\
      as_seq h1 buf == Seq.update_sub #a #(v len) (as_seq h0 buf) (v start) (v n) (spec h0))

(** Loop combinator with just memory safety specification *)
inline_for_extraction noextract
val loop_nospec:
    #h0:mem
  -> #a:Type0
  -> #len:size_t
  -> n:size_t
  -> buf:lbuffer a len
  -> impl: (i:size_t{v i < v n} -> Stack unit
      (requires fun h -> modifies (loc  buf) h0 h)
      (ensures  fun _ _ h1 -> modifies (loc  buf) h0 h1)) ->
  Stack unit
    (requires fun h -> h0 == h /\ live h0 buf)
    (ensures  fun _ _ h1 -> modifies (loc  buf) h0 h1)

(**
* A generalized loop combinator paremetrized by its state (e.g. an accumulator)
*
* Arguments:
* - [h0] the heap when entering the loop. I couldn't factor it out because the specification of the body dedpends on it
* - [n] the number of iterations
* - [a_spec] the type for the specification state (may depend on the loop index)
* - [refl] a ghost function that reflects the Low* state in an iteration as [a_spec]
* - [footprint] locations modified by the loop (may depend on the loop index)
* - [spec] a specification of how the body of the loop modifies the state
* - [impl] the body of the loop as a Stack function
*)
let loop_inv
  (h0:mem)
  (n:size_t)
  (a_spec:(i:size_nat{i <= v n} -> Type))
  (refl:(mem -> i:size_nat{i <= v n} -> GTot (a_spec i)))
  (footprint:(i:size_nat{i <= v n} -> GTot B.loc))
  (spec:(mem -> GTot (i:size_nat{i < v n} -> a_spec i -> a_spec (i + 1))))
  (i:size_nat{i <= v n})
  (h:mem):
  Type0
=
  modifies (footprint i) h0 h /\
  refl h i == Loop.repeat_gen i a_spec (spec h0) (refl h0 0)

inline_for_extraction noextract
val loop:
    h0:mem
  -> n:size_t
  -> a_spec:(i:size_nat{i <= v n} -> Type)
  -> refl:(mem -> i:size_nat{i <= v n} -> GTot (a_spec i))
  -> footprint:(i:size_nat{i <= v n} -> GTot B.loc)
  -> spec:(mem -> GTot (i:size_nat{i < v n} -> a_spec i -> a_spec (i + 1)))
  -> impl:(i:size_t{v i < v n} -> Stack unit
      (requires loop_inv h0 n a_spec refl footprint spec (v i))
      (ensures  fun _ _ -> loop_inv h0 n a_spec refl footprint spec (v i + 1))) ->
  Stack unit
    (requires fun h -> h0 == h)
    (ensures  fun _ _ -> loop_inv h0 n a_spec refl footprint spec (v n))

(** Invariant for Loop1: modifies only one Buffer *)
let loop1_inv
    (h0:mem)
    (n:size_t)
    (b: Type)
    (blen: size_t)
    (write:lbuffer b blen)
    (spec:(mem -> GTot (i:size_nat{i < v n} -> Seq.lseq b (v blen) -> Seq.lseq b (v blen))))
    (i:size_nat{i <= v n})
    (h:mem):
    Type0
=
  modifies (loc  write) h0 h /\
  as_seq h write == Loop.repeati i (spec h0) (as_seq h0 write)

(** Loop which modifies a single buffer [write] *)
inline_for_extraction noextract
val loop1:
    #b:Type
  -> #blen:size_t
  -> h0:mem
  -> n:size_t
  -> write:lbuffer b blen
  -> spec:(mem -> GTot (i:size_nat{i < v n} -> Seq.lseq b (v blen) -> Seq.lseq b (v blen)))
  -> impl:(i:size_t{v i < v n} -> Stack unit
     (requires loop1_inv h0 n b blen write spec (v i))
     (ensures  fun _ _ -> loop1_inv h0 n b blen write spec (v i + 1))) ->
  Stack unit
    (requires fun h -> h0 == h)
    (ensures  fun _ _ -> loop1_inv h0 n b blen write spec (v n))


(** Invariant for Loop2: modifies two Buffers *)
let loop2_inv
  (#b0:Type)
  (#blen0:size_t)
  (#b1:Type)
  (#blen1:size_t)
  (h0:mem)
  (n:size_t)
  (write0:lbuffer b0 blen0)
  (write1:lbuffer b1 blen1)
  (spec:(mem -> GTot (i:size_nat{i < v n}
             -> (Seq.lseq b0 (v blen0)) & (Seq.lseq b1 (v blen1))
             -> (Seq.lseq b0 (v blen0)) & (Seq.lseq b1 (v blen1)))))
  (i:size_nat{i <= v n})
  (h:mem):
  Type0
=
  modifies (loc  write0 |+| loc  write1) h0 h /\
  (let s0, s1 = Loop.repeati i (spec h0) (as_seq h0 write0, as_seq h0 write1) in
   as_seq h write0 == s0 /\ as_seq h write1 == s1)

(** Loop which modifies two buffers [write0] and [write1] *)
inline_for_extraction noextract
val loop2:
    #b0:Type
  -> #blen0:size_t
  -> #b1:Type
  -> #blen1:size_t
  -> h0:mem
  -> n:size_t
  -> write0:lbuffer b0 blen0
  -> write1:lbuffer b1 blen1
  -> spec:(mem -> GTot (i:size_nat{i < v n}
              -> (Seq.lseq b0 (v blen0) & Seq.lseq b1 (v blen1))
              -> (Seq.lseq b0 (v blen0) & Seq.lseq b1 (v blen1))))
  -> impl:(i:size_t{v i < v n} -> Stack unit
      (requires loop2_inv #b0 #blen0 #b1 #blen1 h0 n write0 write1 spec (v i))
      (ensures  fun _ _  -> loop2_inv #b0 #blen0 #b1 #blen1 h0 n write0 write1 spec (v i + 1))) ->
  Stack unit
    (requires fun h -> h0 == h)
    (ensures  fun _ _  -> loop2_inv #b0 #blen0 #b1 #blen1 h0 n write0 write1 spec (v n))

(**
* Allocates a mutable buffer [b] in the stack, calls [impl b] and ovewrites the contents
* of [b] before returning.
*
<* `spec` is the functional post-condition of `impl`, it only takes the final memory
* because the initial memory is determined by `h`

* [spec_inv] is used to propagate the post-condition of [impl] to the final memory
* after popping the stack frame
*)
inline_for_extraction noextract
val salloc1:
    #a:Type
  -> #res:Type
  -> h:mem
  -> len:size_t{0 < v len}
  -> x:a
  -> footprint:Ghost.erased B.loc
  -> spec: (res -> mem -> GTot Type0)
  -> spec_inv:(h1:mem -> h2:mem -> h3:mem -> r:res -> Lemma
      (requires
        B.modifies (B.loc_none) h h1 /\
        B.modifies (B.loc_union (B.loc_all_regions_from false (get_tip h1))
                            (Ghost.reveal footprint)) h1 h2 /\
        B.modifies (B.loc_region_only false (get_tip h1)) h2 h3 /\
        ~(live_region h (get_tip h1)) /\
        spec r h2)
      (ensures  spec r h3))
  -> impl:(b:lbuffer a len -> Stack res
      (requires fun h0 ->
	let b:buffer a = b in
        B.modifies (B.loc_none)  h h0 /\ ~(live_region h (get_tip h0)) /\
        B.frameOf b == get_tip h0 /\ B.live h0 b /\ B.as_seq h0 b == Seq.create (v len) x)
      (ensures  fun h0 r h1 ->
        B.modifies (B.loc_union (B.loc_all_regions_from false (get_tip h0))
                              (Ghost.reveal footprint)) h0 h1 /\
        spec r h1)) ->
  Stack res
    (requires fun h0 -> h0 == h)
    (ensures  fun h0 r h1 -> modifies (Ghost.reveal footprint) h0 h1 /\ spec r h1)

inline_for_extraction noextract
val salloc1_trivial:
    #a:Type
  -> #res:Type
  -> h:mem
  -> len:size_t{0 < v len}
  -> x:a
  -> footprint:Ghost.erased B.loc
  -> spec: (res -> mem -> GTot Type0)
  -> impl:(b:lbuffer a len -> Stack res
      (requires fun h0 ->
        let b : buffer a = b in
        B.modifies (B.loc_none) h h0 /\ ~(live_region h (get_tip h0)) /\
        B.frameOf b == get_tip h0 /\ B.live h0 b /\ B.as_seq h0 b == Seq.create (v len) x)
      (ensures  fun h0 r h1 ->
        B.modifies (B.loc_union (B.loc_all_regions_from false (get_tip h0))
                              (Ghost.reveal footprint)) h0 h1 /\
        spec r h1)) ->
  Stack res
    (requires fun h0 -> h0 == h /\
      (forall (h1 h2 h3:mem) (r:res).
        (B.modifies (B.loc_none) h h1 /\
         B.modifies (B.loc_union (B.loc_all_regions_from false (get_tip h1))
                               (Ghost.reveal footprint)) h1 h2 /\
         B.modifies (B.loc_region_only false (get_tip h1)) h2 h3 /\
         ~(live_region h (get_tip h1)) /\
         spec r h2) ==> spec r h3))
    (ensures  fun h0 r h1 -> modifies (Ghost.reveal footprint) h0 h1 /\ spec r h1)

inline_for_extraction noextract
val salloc_nospec:
    #a:Type
  -> #res:Type
  -> h:mem
  -> len:size_t{0 < v len}
  -> x:a
  -> footprint:Ghost.erased B.loc
  -> impl:(b:lbuffer a len -> Stack res
      (requires fun h0 ->
	let b:buffer a = b in
        modifies0 h h0 /\ ~(live_region h (get_tip h0)) /\
        B.frameOf b == get_tip h0 /\ B.live h0 b /\ B.as_seq h0 b == Seq.create (v len) x)
      (ensures  fun h0 r h1 ->
        modifies (B.loc_union (B.loc_all_regions_from false (get_tip h0))
                              (Ghost.reveal footprint)) h0 h1)) ->
  Stack res
    (requires fun h0 -> h0 == h)
    (ensures  fun h0 r h1 -> modifies (Ghost.reveal footprint) h0 h1)

inline_for_extraction noextract
val loopi_blocks:
    #a:Type0
  -> #b:Type0
  -> #blen:size_t
  -> blocksize:size_t{v blocksize > 0}
  -> inpLen:size_t
  -> inp:lbuffer a inpLen
  -> spec_f:(i:nat{i < v inpLen / v blocksize}
              -> Seq.lseq a (v blocksize)
              -> Seq.lseq b (v blen)
              -> Seq.lseq b (v blen))
  -> spec_l:(i:nat{i == v inpLen / v blocksize}
              -> len:size_nat{len == v inpLen % v blocksize}
              -> s:Seq.lseq a len
              -> Seq.lseq b (v blen)
              -> Seq.lseq b (v blen))
  -> f:(i:size_t{v i < v inpLen / v blocksize}
       -> inp:lbuffer a blocksize
       -> w:lbuffer b blen -> Stack unit
          (requires fun h ->
            live h inp /\ live h w /\ disjoint inp w)
          (ensures  fun h0 _ h1 ->
            modifies (loc  w) h0 h1 /\
            as_seq h1 w == spec_f (v i) (as_seq h0 inp) (as_seq h0 w)))
  -> l:(i:size_t{v i == v inpLen / v blocksize}
       -> len:size_t{v len == v inpLen % v blocksize}
       -> inp:lbuffer a len
       -> w:lbuffer b blen -> Stack unit
          (requires fun h ->
            live h inp /\ live h w /\ disjoint inp w)
          (ensures  fun h0 _ h1 ->
            modifies (loc  w) h0 h1 /\
            as_seq h1 w == spec_l (v i) (v len) (as_seq h0 inp) (as_seq h0 w)))
  -> write:lbuffer b blen ->
  Stack unit
    (requires fun h -> live h inp /\ live h write /\ disjoint inp write)
    (ensures  fun h0 _ h1 ->
      modifies (loc  write) h0 h1 /\
      as_seq h1 write ==
      Seq.repeati_blocks #a #(Seq.lseq b (v blen)) (v blocksize) (as_seq h0 inp) spec_f spec_l (as_seq h0 write))

inline_for_extraction noextract
val loop_blocks:
    #a:Type0
  -> #b:Type0
  -> #blen:size_t
  -> blocksize:size_t{v blocksize > 0}
  -> inpLen:size_t
  -> inp:lbuffer a inpLen
  -> spec_f:(Seq.lseq a (v blocksize)
              -> Seq.lseq b (v blen)
              -> Seq.lseq b (v blen))
  -> spec_l:(len:size_nat{len == v inpLen % v blocksize}
              -> s:Seq.lseq a len
              -> Seq.lseq b (v blen)
              -> Seq.lseq b (v blen))
  -> f:(inp:lbuffer a blocksize
       -> w:lbuffer b blen -> Stack unit
          (requires fun h ->
            live h inp /\ live h w /\ disjoint inp w)
          (ensures  fun h0 _ h1 ->
            modifies (loc  w) h0 h1 /\
            as_seq h1 w == spec_f (as_seq h0 inp) (as_seq h0 w)))
  -> l:(len:size_t{v len == v inpLen % v blocksize}
       -> inp:lbuffer a len
       -> w:lbuffer b blen -> Stack unit
          (requires fun h ->
            live h inp /\ live h w /\ disjoint inp w)
          (ensures  fun h0 _ h1 ->
            modifies (loc  w) h0 h1 /\
            as_seq h1 w == spec_l (v len) (as_seq h0 inp) (as_seq h0 w)))
  -> write:lbuffer b blen ->
  Stack unit
    (requires fun h -> live h inp /\ live h write /\ disjoint inp write)
    (ensures  fun h0 _ h1 ->
      modifies (loc  write) h0 h1 /\
      as_seq h1 write ==
      Seq.repeat_blocks #a #(Seq.lseq b (v blen)) (v blocksize) (as_seq h0 inp) spec_f spec_l (as_seq h0 write))


(** Fill a buffer with a total function *)
inline_for_extraction
val fillT:
    #a:Type
  -> clen:size_t
  -> o:lbuffer a clen
  -> spec_f:(i:size_nat{i < v clen} -> a)
  -> f:(i:size_t{v i < v clen} -> r:a{r == spec_f (size_v i)})
  -> Stack unit
    (requires fun h0 -> live h0 o)
    (ensures  fun h0 _ h1 ->
      live h1 o /\ modifies (loc  o) h0 h1 /\
      as_seq h1 o == Seq.createi #a (v clen) spec_f)

(** Fill a buffer with a stateful function *)
inline_for_extraction
val fill:
    #a:Type
  -> h0:mem 
  -> clen:size_t
  -> o:lbuffer a clen
  -> spec:(mem -> GTot(i:size_nat{i < v clen} -> a))
  -> impl:(i:size_t{v i < v clen} -> Stack unit
          (requires fun h -> modifies (loc  o) h0 h)
          (ensures  fun h _ h' ->
            modifies (loc  o) h h' /\
            as_seq h' o == Seq.upd (as_seq h o) (v i) (spec h0 (v i))))
  -> Stack unit
    (requires fun h -> h == h0 /\ live h0 o)
    (ensures  fun h _ h' ->
      modifies (loc  o) h h' /\
      as_seq h' o == Seq.createi #a (v clen) (spec h0))


(** Map a total function on a buffer *)
inline_for_extraction
val mapT:
    #t:buftype
  -> #a:Type
  -> #b:Type
  -> clen:size_t
  -> o:lbuffer b clen
  -> f:(a -> Tot b)
  -> i:lbuffer_t t a clen ->
  Stack unit
    (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
    (ensures  fun h0 _ h1 ->
      modifies (loc  o) h0 h1 /\
      as_seq h1 o == Seq.map f (as_seq h0 i))

(** Map a total function on a buffer *)
inline_for_extraction
val mapiT:
    #t:buftype
  -> #a:Type
  -> #b:Type
  -> clen:size_t
  -> o:lbuffer b clen
  -> f:(i:size_t{v i < v clen} -> x:a -> r:b)
  -> i:lbuffer_t t a clen ->
  Stack unit
    (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
    (ensures  fun h0 _ h1 ->
      modifies (loc  o) h0 h1 /\
      as_seq h1 o == Seq.mapi (fun i -> f (size i)) (as_seq h0 i))

