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

(** Definition of a mutable Buffer *)
let buffer (a:Type0) = B.buffer a

(** Definition of an immutable Buffer *)
let ibuffer (a:Type0) = IB.ibuffer a

(** Length of buffers *)
val length: #a:Type0 -> b:buffer a -> GTot (r:size_nat{r == B.length b})
val ilength: #a:Type0 -> b:ibuffer a -> GTot (r:size_nat{r == IB.length b})

(** Definition of fixed length mutable and immutable Buffers *)
let lbuffer (a:Type0) (len:size_nat) = b:buffer a {length b == len}
let ilbuffer (a:Type0) (len:size_nat) = b:IB.ibuffer a {IB.length b == len}

(** Alias for mutable buffer of bytes *)
let lbytes len = lbuffer uint8 len

(** Liveness of buffers *)
let live (#a:Type0) (#rrel #rel:LMB.srel a) (h:HS.mem) (b:LMB.mbuffer a rrel rel) = B.live #a #rrel #rel h b

(** Generalized modification clause for Buffer locations *)
let modifies
  (s: B.loc)
  (h1 h2: HS.mem):
  GTot Type0 = B.modifies s h1 h2

(** Disjointness clause for Buffers *)
let disjoint
  (#a1 #a2:Type0)
  (#rrel1 #rel1:LMB.srel a1)
  (#rrel2 #rel2:LMB.srel a2)
  (b1:LMB.mbuffer a1 rrel1 rel1)
  (b2:LMB.mbuffer a2 rrel2 rel2):
  GTot Type0 = B.loc_disjoint (B.loc_buffer b1) (B.loc_buffer b2)

(** Modification for no Buffer *)
let modifies0 (h1 h2: HS.mem) : GTot Type0 = B.modifies (B.loc_none) h1 h2

(** Modification clause for one Buffer *)
let modifies1
  (#a:Type0)
  (#len:size_nat)
  (b: lbuffer a len)
  (h1 h2: HS.mem):
  GTot Type0 = B.modifies (B.loc_buffer b) h1 h2

(** Modification clause for two Buffers *)
let modifies2
  (#a0:Type0)
  (#a1:Type0)
  (#len0:size_nat)
  (#len1:size_nat)
  (b0: lbuffer a0 len0)
  (b1: lbuffer a1 len1)
  (h1 h2: HS.mem):
  GTot Type0 = B.modifies (B.loc_union (B.loc_buffer b0) (B.loc_buffer b1)) h1 h2

(** Modification clause for three Buffers *)
let modifies3
  (#a0:Type0)
  (#a1:Type0)
  (#a2:Type0)
  (#len0:size_nat)
  (#len1:size_nat)
  (#len2:size_nat)
  (b0: lbuffer a0 len0)
  (b1: lbuffer a1 len1)
  (b2: lbuffer a1 len1)
  (h1 h2: HS.mem):
  GTot Type0 = B.modifies (B.loc_union (B.loc_buffer b0) (B.loc_union (B.loc_buffer b1) (B.loc_buffer b2))) h1 h2

(** Ghost reveal a Buffer as its Pure Sequence *)
let as_seq
  (#a:Type0)
  (#len:size_nat)
  (h:HS.mem)
  (b:lbuffer a len):
  GTot (Seq.lseq a len) = B.as_seq h b

let ias_seq
  (#a:Type0)
  (#len:size_nat)
  (h:HS.mem)
  (b:ilbuffer a len):
  GTot (Seq.lseq a len) = IB.as_seq h b

(** Ghost view of a subset of a mutable Buffer *)
let gsub
  (#a:Type0)
  (#len:size_nat)
  (b:lbuffer a len)
  (start:size_t)
  (n:size_t{v start + v n <= len})
  = B.gsub b (size_to_UInt32 start) (size_to_UInt32 n)

val as_seq_gsub:
    #a:Type0
  -> #len:size_nat
  -> h:HS.mem
  -> b:lbuffer a len
  -> start:size_t
  -> n:size_t{v start + v n <= len} ->
  Lemma
   (as_seq h (gsub #a #len b start n) ==
    Seq.sub #a #len (as_seq h b) (v start) (v n))
  [SMTPat (Seq.sub #a #len (as_seq h b) (v start) (v n))]

(** Subset of a mutable Buffer *)
inline_for_extraction
val sub:
    #a:Type0
  -> #len:size_nat
  -> #olen:size_nat
  -> b:lbuffer a len
  -> start:size_t
  -> n:size_t{v start + v n <= len /\ v n == olen} ->
  Stack (lbuffer a olen)
    (requires fun h0 -> B.live h0 b)
    (ensures  fun h0 r h1 -> h0 == h1 /\ r == gsub b start n)

(** Ghost view of a subset of an immutable Buffer *)
let igsub
  (#a:Type0)
  (#len:size_nat)
  (b:ilbuffer a len)
  (start:size_t)
  (n:size_t{v start + v n <= len})
  = IB.igsub b (size_to_UInt32 start) (size_to_UInt32 n)

val as_seq_igsub:
    #a:Type0
  -> #len:size_nat
  -> h:HS.mem
  -> b:ilbuffer a len
  -> start:size_t
  -> n:size_t{v start + v n <= len} ->
  Lemma
    (ias_seq h (igsub #a #len b start n) ==
     Seq.sub #a #len (ias_seq h b) (v start) (v n))
  [SMTPat (Seq.sub #a #len (ias_seq h b) (v start) (v n))]

(** Subset of an immutable Buffer *)
inline_for_extraction
val isub:
    #a:Type0
  -> #len:size_nat
  -> #olen:size_nat
  -> b:ilbuffer a len
  -> start:size_t
  -> n:size_t{v start + v n <= len /\ v n == olen} ->
  Stack (ilbuffer a olen)
    (requires fun h0 -> IB.live h0 b)
    (ensures  fun h0 r h1 -> h0 == h1 /\ r == igsub b start n)

(** Access a specific value in an mutable Buffer *)
inline_for_extraction
val index:
    #a:Type0
  -> #len:size_nat
  -> b:lbuffer a len
  -> i:size_t{v i < len} ->
  Stack a
    (requires fun h0 -> B.live h0 b)
    (ensures  fun h0 r h1 -> h0 == h1 /\
      r == Seq.index #a #len (as_seq h1 b) (v i))

(** Access a specific value in an immutable Buffer *)
inline_for_extraction
val iindex:
    #a:Type0
  -> #len:size_nat
  -> b:ilbuffer a len
  -> i:size_t{v i < len} ->
  Stack a
    (requires fun h0 -> IB.live h0 b)
    (ensures  fun h0 r h1 -> h0 == h1 /\
      r == Seq.index #a #len (ias_seq h1 b) (v i))

(** Update a specific value in a mutable Buffer *)
inline_for_extraction
val upd:
    #a:Type0
  -> #len:size_nat{len > 0}
  -> b:lbuffer a len
  -> i:size_t{v i < len}
  -> x:a ->
  Stack unit
    (requires fun h0 -> B.live h0 b)
    (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer b) h0 h1 /\ B.live h1 b /\
      as_seq h1 b == Seq.upd #a #len (as_seq h0 b) (v i) x)

(** Operator definition to update a mutable Buffer *)
inline_for_extraction
let op_Array_Assignment #a #len = upd #a #len

(** Operator definition to access a mutable Buffer *)
inline_for_extraction
let op_Array_Access #a #len = index #a #len

(** Operator definition to access a Buffer as a Sequence *)
inline_for_extraction
let op_String_Access #a #r0 #r1 m b = B.as_seq #a #r0 #r1 m b

(** Access to the pure sequence-based value associated to an index of a mutable Buffer  *)
(* We don't have access to Lib.Sequence.fst
   to get the fact `Lib.Sequence.index == FStar.Seq.index` *)
inline_for_extraction
val bget:
    #a:Type0
  -> #len:size_nat
  -> h:mem
  -> b:lbuffer a len
  -> i:size_nat{i < len} ->
  GTot (r:a{r == B.get h b i /\ r == Seq.index #a #len (as_seq h b) i})

(** Access to the pure sequence-based value associated to an index of an immutable Buffer  *)
(* We don't have access to Lib.Sequence.fst
   to get the fact `Lib.Sequence.index == FStar.Seq.index` *)
inline_for_extraction
val ibget:
    #a:Type0
  -> #len:size_nat
  -> h:mem
  -> b:ilbuffer a len
  -> i:size_nat{i < len} ->
  GTot (r:a{r == B.get h b i /\ r == Seq.index #a #len (ias_seq h b) i})

(** Allocate a fixed-length mutable Buffer and initialize it to value [init] *)
inline_for_extraction
val create:
    #a:Type0
  -> #len:size_nat
  -> clen:size_t{v clen == len}
  -> init:a ->
  StackInline (lbuffer a len)
    (requires fun h0 -> len > 0)
    (ensures  fun h0 b h1 ->
      B.alloc_post_mem_common b h0 h1 (Seq.create len init) /\
      B.frameOf b = HS.get_tip h0)

(** Allocate a fixed-length mutable Buffer based on an existing List *)
inline_for_extraction noextract
val createL:
    #a:Type0
  -> init:list a{List.Tot.length init <= max_size_t} ->
  StackInline (lbuffer a (normalize_term (List.Tot.length init)))
    (requires fun h0 -> B.alloca_of_list_pre #a init)
    (ensures fun h0 b h1 ->
      B.alloc_post_mem_common b h0 h1 (Seq.of_list init) /\
      B.frameOf b = HS.get_tip h0)

(** Recall the value of a top-level Buffer *)
inline_for_extraction noextract
val recall:
    #a:Type
  -> #len:size_nat
  -> b:lbuffer a len ->
  Stack unit
    (requires fun _ -> B.recallable b)
    (ensures  fun m0 _ m1 -> m0 == m1 /\ B.live m1 b)

(** Allocate a top-level fixed-length mutable Buffer and initialize it to value [init] *)
inline_for_extraction noextract
val createL_global:
    #a:Type0
  -> init:list a{normalize (List.Tot.length init <= max_size_t)} ->
  ST (b:lbuffer a (normalize_term (List.Tot.length init)){
      B.frameOf b == HyperStack.root /\ B.recallable b})
    (requires fun h0 -> B.gcmalloc_of_list_pre #a HyperStack.root init)
    (ensures  fun h0 b h1 -> B.alloc_post_mem_common b h0 h1 (Seq.of_list init))

private
let cpred (#a:Type0) (s:Seq.seq a) : B.spred a = fun s1 -> FStar.Seq.equal s s1

(** Allocate a top-level fixed-length immutable Buffer and initialize it to value [init] *)
inline_for_extraction noextract
val icreateL_global:
    #a:Type0
  -> init:list a{normalize (List.Tot.length init <= max_size_t)} ->
  ST (b:ilbuffer a (normalize_term (List.Tot.length init)){
      B.frameOf b == HyperStack.root /\ B.recallable b /\
      B.witnessed b (cpred (Seq.of_list init))})
    (requires fun h0 -> B.gcmalloc_of_list_pre #a HyperStack.root init)
    (ensures  fun h0 b h1 -> B.alloc_post_mem_common b h0 h1 (Seq.of_list init))

(** Recall the liveness and content of a global immutable Buffer *)
inline_for_extraction noextract
val recall_contents:
    #a:Type0
  -> #len:size_nat{len <= max_size_t}
  -> b:ilbuffer a len
  -> s:Seq.lseq a len ->
  ST unit
    (requires fun h0 -> (B.recallable b \/ live h0 b) /\ B.witnessed b (cpred s))
    (ensures  fun h0 _ h1 -> h0 == h1 /\ live h0 b /\ ias_seq h0 b == s)

(** Copy a mutable Buffer in another mutable Buffer *)
inline_for_extraction
val copy:
    #a:Type
  -> #len:size_nat
  -> o:lbuffer a len
  -> clen:size_t{v clen == len}
  -> i:lbuffer a len ->
  Stack unit
    (requires fun h0 -> B.live h0 o /\ B.live h0 i /\ B.disjoint i o)
    (ensures  fun h0 _ h1 ->
      B.live h1 o /\ B.live h1 i /\ B.modifies (B.loc_buffer o) h0 h1 /\
      as_seq h1 o == as_seq h0 i)

(** Copy an immutable Buffer in a mutable Buffer *)
inline_for_extraction
val icopy:
    #a:Type
  -> #len:size_nat
  -> o:lbuffer a len
  -> clen:size_t{v clen == len}
  -> i:ilbuffer a len ->
  Stack unit
    (requires fun h0 -> B.live h0 o /\ B.live h0 i /\ B.disjoint i o)
    (ensures  fun h0 _ h1 ->
      B.live h1 o /\ B.live h1 i /\ B.modifies (B.loc_buffer o) h0 h1 /\
      as_seq h1 o == ias_seq h0 i)

(**
* Set all elements of a mutable buffer to a specific value
*
* WARNING: don't rely on the extracted implementation for secure erasure,
* C compilers may remove optimize it away.
*)
inline_for_extraction
val memset:
    #a:Type
  -> #blen:size_nat
  -> b:lbuffer a blen
  -> w:a
  -> len:size_t{v len <= blen} ->
  Stack unit
    (requires fun h0 -> live h0 b)
    (ensures  fun h0 _ h1 ->
      modifies1 b h0 h1 /\
      as_seq #a #(v len) h1 (gsub b 0ul len) == Seq.create (v len) w /\
      as_seq #a #(blen - v len) h1 (gsub b len (size blen -! len)) ==
      as_seq #a #(blen - v len) h0 (gsub b len (size blen -! len)))

(** Copy a mutable Buffer in a part of another mutable Buffer *)
inline_for_extraction
val update_sub:
    #a:Type
  -> #len:size_nat
  -> dst:lbuffer a len
  -> start:size_t
  -> n:size_t{v start + v n <= len}
  -> src:lbuffer a (size_v n) ->
  Stack unit
    (requires fun h -> B.live h dst /\ B.live h src /\ B.disjoint dst src)
    (ensures  fun h0 _ h1 -> B.live h1 dst /\ B.modifies (B.loc_buffer dst) h0 h1 /\
      as_seq h1 dst == Seq.update_sub #a #len (as_seq h0 dst) (v start) (v n) (as_seq h0 src))

(** Copy an immutable Buffer in a part of a mutable Buffer *)
inline_for_extraction
val update_isub:
    #a:Type
  -> #len:size_nat
  -> dst:lbuffer a len
  -> start:size_t
  -> n:size_t{v start + v n <= len}
  -> src:ilbuffer a (size_v n) ->
  Stack unit
    (requires fun h -> B.live h dst /\ B.live h src /\ B.disjoint dst src)
    (ensures  fun h0 _ h1 -> B.live h1 dst /\ B.modifies (B.loc_buffer dst) h0 h1 /\
      as_seq h1 dst == Seq.update_sub #a #len (as_seq h0 dst) (v start) (v n) (ias_seq h0 src))

(** Update a part of a mutable Buffer in-place with the application of a function F on another Buffer *)
inline_for_extraction
val update_sub_f:
     #a:Type
  -> #len:size_nat
  -> h0:mem
  -> buf:lbuffer a len
  -> start:size_t
  -> n:size_t{v start + v n <= len}
  -> spec:(mem -> GTot (Seq.lseq a (v n)))
  -> f:(b:lbuffer a (v n) -> Stack unit
      (requires fun h -> h0 == h /\ B.live h b)
      (ensures  fun h0 _ h1 ->
             B.modifies (B.loc_buffer b) h0 h1 /\
             as_seq h1 b == spec h0)) ->
  Stack unit
    (requires fun h -> h0 == h /\ B.live h buf)
    (ensures  fun h0 _ h1 -> B.modifies (B.loc_buffer buf) h0 h1 /\
      as_seq h1 buf == Seq.update_sub #a #len (as_seq h0 buf) (v start) (v n) (spec h0))

inline_for_extraction
val concat2:
    #a:Type0
  -> len0:size_t
  -> s0:lbuffer a (v len0)
  -> len1:size_t{v len0 + v len1 < max_size_t}
  -> s1:lbuffer a (v len1)
  -> s:lbuffer a (v len0 + v len1)
  -> Stack unit
    (requires fun h ->
      B.live h s0 /\ B.live h s1 /\ B.live h s /\
      B.disjoint s s0 /\ B.disjoint s s1)
    (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer s) h0 h1 /\
      as_seq h1 s == Seq.concat (as_seq h0 s0) (as_seq h0 s1))

inline_for_extraction
val concat3:
    #a:Type0
  -> len0:size_t
  -> s0:lbuffer a (v len0)
  -> len1:size_t{v len0 + v len1 < max_size_t}
  -> s1:lbuffer a (v len1)
  -> len2:size_t{v len0 + v len1 + v len2 < max_size_t}
  -> s2:lbuffer a (v len2)
  -> s:lbuffer a (v len0 + v len1 + v len2)
  -> Stack unit
    (requires fun h ->
      B.live h s0 /\ B.live h s1 /\ B.live h s2 /\ B.live h s /\
      B.disjoint s s0 /\ B.disjoint s s1 /\ B.disjoint s s2)
    (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer s) h0 h1 /\
      as_seq h1 s == Seq.concat (Seq.concat (as_seq h0 s0) (as_seq h0 s1)) (as_seq h0 s2))

(** Loop combinator with just memory safety specification *)
inline_for_extraction noextract
val loop_nospec:
    #h0:mem
  -> #a:Type0
  -> #len:size_nat
  -> n:size_t
  -> buf:lbuffer a len
  -> impl: (i:size_t{v i < v n} -> Stack unit
      (requires fun h -> B.modifies (B.loc_buffer buf) h0 h)
      (ensures  fun _ _ h1 -> B.modifies (B.loc_buffer buf) h0 h1)) ->
  Stack unit
    (requires fun h -> h0 == h /\ B.live h0 buf)
    (ensures  fun _ _ h1 -> B.modifies (B.loc_buffer buf) h0 h1)

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
  B.modifies (footprint i) h0 h /\
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
    (blen: size_nat)
    (write:lbuffer b blen)
    (spec:(mem -> GTot (i:size_nat{i < v n} -> Seq.lseq b blen -> Seq.lseq b blen)))
    (i:size_nat{i <= v n})
    (h:mem):
    Type0
=
  B.modifies (B.loc_buffer write) h0 h /\
  as_seq h write == Loop.repeati i (spec h0) (as_seq h0 write)

(** Loop which modifies a single buffer [write] *)
inline_for_extraction noextract
val loop1:
    #b:Type
  -> #blen:size_nat
  -> h0:mem
  -> n:size_t
  -> write:lbuffer b blen
  -> spec:(mem -> GTot (i:size_nat{i < v n} -> Seq.lseq b blen -> Seq.lseq b blen))
  -> impl:(i:size_t{v i < v n} -> Stack unit
     (requires loop1_inv h0 n b blen write spec (v i))
     (ensures  fun _ _ -> loop1_inv h0 n b blen write spec (v i + 1))) ->
  Stack unit
    (requires fun h -> h0 == h)
    (ensures  fun _ _ -> loop1_inv h0 n b blen write spec (v n))


(** Invariant for Loop2: modifies two Buffers *)
let loop2_inv
  (#b0:Type)
  (#blen0:size_nat)
  (#b1:Type)
  (#blen1:size_nat)
  (h0:mem)
  (n:size_t)
  (write0:lbuffer b0 blen0)
  (write1:lbuffer b1 blen1)
  (spec:(mem -> GTot (i:size_nat{i < v n}
             -> (Seq.lseq b0 blen0) & (Seq.lseq b1 blen1)
             -> (Seq.lseq b0 blen0) & (Seq.lseq b1 blen1))))
  (i:size_nat{i <= v n})
  (h:mem):
  Type0
=
  B.modifies (B.loc_union (B.loc_buffer write0) (B.loc_buffer write1)) h0 h /\
  (let s0, s1 = Loop.repeati i (spec h0) (as_seq h0 write0, as_seq h0 write1) in
   as_seq h write0 == s0 /\ as_seq h write1 == s1)

(** Loop which modifies two buffers [write0] and [write1] *)
inline_for_extraction noextract
val loop2:
     #b0:Type
  -> #blen0:size_nat
  -> #b1:Type
  -> #blen1:size_nat
  -> h0:mem
  -> n:size_t
  -> write0:lbuffer b0 blen0
  -> write1:lbuffer b1 blen1
  -> spec:(mem -> GTot (i:size_nat{i < v n}
              -> tuple2 (Seq.lseq b0 blen0) (Seq.lseq b1 blen1)
              -> tuple2 (Seq.lseq b0 blen0) (Seq.lseq b1 blen1)))
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
* `spec` is the functional post-condition of `impl`, it only takes the final memory
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
        modifies0 h h1 /\
        modifies (B.loc_union (B.loc_all_regions_from false (get_tip h1))
                            (Ghost.reveal footprint)) h1 h2 /\
        modifies (B.loc_region_only false (get_tip h1)) h2 h3 /\
        ~(live_region h (get_tip h1)) /\
        spec r h2)
      (ensures  spec r h3))
  -> impl:(b:lbuffer a (v len) -> Stack res
      (requires fun h0 ->
        modifies0 h h0 /\ ~(live_region h (get_tip h0)) /\
        B.frameOf b == get_tip h0 /\ live h0 b /\ as_seq h0 b == Seq.create (v len) x)
      (ensures  fun h0 r h1 ->
        modifies (B.loc_union (B.loc_all_regions_from false (get_tip h0))
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
  -> impl:(b:lbuffer a (v len) -> Stack res
      (requires fun h0 ->
        modifies0 h h0 /\ ~(live_region h (get_tip h0)) /\
        B.frameOf b == get_tip h0 /\ live h0 b /\ as_seq h0 b == Seq.create (v len) x)
      (ensures  fun h0 r h1 ->
        modifies (B.loc_union (B.loc_all_regions_from false (get_tip h0))
                              (Ghost.reveal footprint)) h0 h1 /\
        spec r h1)) ->
  Stack res
    (requires fun h0 -> h0 == h /\
      (forall (h1 h2 h3:mem) (r:res).
        (modifies0 h h1 /\
         modifies (B.loc_union (B.loc_all_regions_from false (get_tip h1))
                               (Ghost.reveal footprint)) h1 h2 /\
         modifies (B.loc_region_only false (get_tip h1)) h2 h3 /\
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
  -> impl:(b:lbuffer a (v len) -> Stack res
      (requires fun h0 ->
        modifies0 h h0 /\ ~(live_region h (get_tip h0)) /\
        B.frameOf b == get_tip h0 /\ live h0 b /\ as_seq h0 b == Seq.create (v len) x)
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
  -> #blen:size_nat
  -> blocksize:size_t{v blocksize > 0}
  -> inpLen:size_t
  -> inp:lbuffer a (v inpLen)
  -> spec_f:(i:nat{i < v inpLen / v blocksize}
              -> Seq.lseq a (v blocksize)
              -> Seq.lseq b blen
              -> Seq.lseq b blen)
  -> spec_l:(i:nat{i == v inpLen / v blocksize}
              -> len:size_nat{len == v inpLen % v blocksize}
              -> s:Seq.lseq a len
              -> Seq.lseq b blen
              -> Seq.lseq b blen)
  -> f:(i:size_t{v i < v inpLen / v blocksize}
       -> inp:lbuffer a (v blocksize)
       -> w:lbuffer b blen -> Stack unit
          (requires fun h ->
            B.live h inp /\ B.live h w /\ B.disjoint inp w)
          (ensures  fun h0 _ h1 ->
            B.modifies (B.loc_buffer w) h0 h1 /\
            as_seq h1 w == spec_f (v i) (as_seq h0 inp) (as_seq h0 w)))
  -> l:(i:size_t{v i == v inpLen / v blocksize}
       -> len:size_t{v len == v inpLen % v blocksize}
       -> inp:lbuffer a (v len)
       -> w:lbuffer b blen -> Stack unit
          (requires fun h ->
            B.live h inp /\ B.live h w /\ B.disjoint inp w)
          (ensures  fun h0 _ h1 ->
            B.modifies (B.loc_buffer w) h0 h1 /\
            as_seq h1 w == spec_l (v i) (v len) (as_seq h0 inp) (as_seq h0 w)))
  -> write:lbuffer b blen ->
  Stack unit
    (requires fun h -> B.live h inp /\ B.live h write /\ B.disjoint inp write)
    (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer write) h0 h1 /\
      as_seq h1 write ==
      Seq.repeati_blocks #a #(Seq.lseq b blen) (v blocksize) (as_seq h0 inp) spec_f spec_l (as_seq h0 write))

inline_for_extraction noextract
val loop_blocks:
    #a:Type0
  -> #b:Type0
  -> #blen:size_nat
  -> blocksize:size_t{v blocksize > 0}
  -> inpLen:size_t
  -> inp:lbuffer a (v inpLen)
  -> spec_f:(Seq.lseq a (v blocksize)
              -> Seq.lseq b blen
              -> Seq.lseq b blen)
  -> spec_l:(len:size_nat{len == v inpLen % v blocksize}
              -> s:Seq.lseq a len
              -> Seq.lseq b blen
              -> Seq.lseq b blen)
  -> f:(inp:lbuffer a (v blocksize)
       -> w:lbuffer b blen -> Stack unit
          (requires fun h ->
            B.live h inp /\ B.live h w /\ B.disjoint inp w)
          (ensures  fun h0 _ h1 ->
            B.modifies (B.loc_buffer w) h0 h1 /\
            as_seq h1 w == spec_f (as_seq h0 inp) (as_seq h0 w)))
  -> l:(len:size_t{v len == v inpLen % v blocksize}
       -> inp:lbuffer a (v len)
       -> w:lbuffer b blen -> Stack unit
          (requires fun h ->
            B.live h inp /\ B.live h w /\ B.disjoint inp w)
          (ensures  fun h0 _ h1 ->
            B.modifies (B.loc_buffer w) h0 h1 /\
            as_seq h1 w == spec_l (v len) (as_seq h0 inp) (as_seq h0 w)))
  -> write:lbuffer b blen ->
  Stack unit
    (requires fun h -> B.live h inp /\ B.live h write /\ B.disjoint inp write)
    (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer write) h0 h1 /\
      as_seq h1 write ==
      Seq.repeat_blocks #a #(Seq.lseq b blen) (v blocksize) (as_seq h0 inp) spec_f spec_l (as_seq h0 write))

open FStar.Mul

(** Fills a buffer block by block using a function with an accumulator *)
inline_for_extraction noextract
val fill_blocks:
    #t:Type0
  -> h0:mem
  -> len:size_t
  -> n:size_t{v n * v len <= max_size_t}
  -> output:lbuffer t (v n * v len)
  -> a_spec:(i:size_nat{i <= v n} -> Type)
  -> refl:(mem -> i:size_nat{i <= v n} -> GTot (a_spec i))
  -> footprint:(i:size_nat{i <= v n} -> GTot
      (l:B.loc{B.loc_disjoint l (B.loc_buffer output) /\
               B.address_liveness_insensitive_locs `B.loc_includes` l}))
  -> spec:(mem -> GTot (i:size_nat{i < v n} -> a_spec i -> a_spec (i + 1) & Seq.lseq t (v len)))
  -> impl:(i:size_t{v i < v n} -> block:lbuffer t (v len) -> Stack unit
      (requires fun h1 ->
        live h1 block /\
        B.loc_buffer output `B.loc_includes` B.loc_buffer block /\
        modifies (B.loc_union (footprint (v i)) (B.loc_buffer output)) h0 h1)
      (ensures  fun h1 _ h2 ->
        let s, b = spec h0 (v i) (refl h1 (v i)) in
        footprint (v i + 1) `B.loc_includes` footprint (v i) /\
        B.modifies (B.loc_union (footprint (v i + 1)) (B.loc_buffer block)) h1 h2 /\
        refl h2 (v i + 1) == s /\ as_seq h2 block == b)) ->
  Stack unit
    (requires fun h -> h0 == h /\ live h output)
    (ensures  fun _ _ h1 ->
      let s, o = Seq.generate_blocks (v len) (v n) a_spec (spec h0) (refl h0 0) in
      B.modifies (B.loc_union (footprint (v n)) (B.loc_buffer output)) h0 h1 /\
      refl h1 (v n) == s /\
      as_seq #_ #(v n * v len) h1 (gsub output (size 0) (n *! len)) == o)

(** Fill a buffer with a total function *)
inline_for_extraction
val fillT:
    #a:Type
  -> clen:size_t
  -> o:lbuffer a (v clen)
  -> spec_f:(i:size_nat{i < v clen} -> a)
  -> f:(i:size_t{v i < v clen} -> r:a{r == spec_f (size_v i)})
  -> Stack unit
    (requires fun h0 -> B.live h0 o)
    (ensures  fun h0 _ h1 ->
      B.live h1 o /\ B.modifies (B.loc_buffer o) h0 h1 /\
      as_seq h1 o == Seq.createi #a (v clen) spec_f)

(** Fill a buffer with a stateful function *)
inline_for_extraction
val fill:
    #a:Type
  -> h0:mem 
  -> clen:size_t
  -> o:lbuffer a (v clen)
  -> spec:(mem -> GTot(i:size_nat{i < v clen} -> a))
  -> impl:(i:size_t{v i < v clen} -> Stack unit
          (requires fun h -> B.modifies (B.loc_buffer o) h0 h)
          (ensures  fun h _ h' ->
            B.modifies (B.loc_buffer o) h h' /\
            as_seq h' o == Seq.upd (as_seq h o) (v i) (spec h0 (v i))))
  -> Stack unit
    (requires fun h -> h == h0 /\ B.live h0 o)
    (ensures  fun h _ h' ->
      B.modifies (B.loc_buffer o) h h' /\
      as_seq h' o == Seq.createi #a (v clen) (spec h0))

(** Map a total function on a buffer *)
inline_for_extraction
val mapT:
    #a:Type
  -> #b:Type
  -> clen:size_t
  -> o:lbuffer b (v clen)
  -> f:(a -> Tot b)
  -> i:lbuffer a (v clen) ->
  Stack unit
    (requires fun h0 -> B.live h0 o /\ B.live h0 i /\ B.disjoint o i)
    (ensures  fun h0 _ h1 ->
      B.live h1 o /\ B.live h1 i /\ B.modifies (B.loc_buffer o) h0 h1 /\
      as_seq h1 o == Seq.map f (as_seq h0 i))

(** Map a total function (depending on the index) on a buffer *)
inline_for_extraction
val mapiT:
    #a:Type
  -> #b:Type
  -> clen:size_t
  -> o:lbuffer b (v clen)
  -> spec_f:(i:size_nat{i < v clen} -> a -> Tot b)
  -> f:(i:size_t{v i < v clen} -> x:a -> r:b{r == spec_f (v i) x})
  -> i:lbuffer a (v clen) ->
  Stack unit
    (requires fun h0 -> B.live h0 o /\ B.live h0 i /\ B.disjoint o i)
    (ensures  fun h0 _ h1 ->
      B.live h1 o /\ B.live h1 i /\ B.modifies (B.loc_buffer o) h0 h1 /\
      as_seq h1 o == Seq.mapi spec_f (as_seq h0 i))

(** Map a total function on an immutable buffer *)
inline_for_extraction
val imapT:
    #a:Type
  -> #b:Type
  -> #len:size_nat
  -> o:lbuffer b len
  -> clen:size_t{v clen == len}
  -> f:(a -> Tot b)
  -> i:ilbuffer a len ->
  Stack unit
    (requires fun h0 -> B.live h0 o /\ B.live h0 i /\ B.disjoint o i)
    (ensures  fun h0 _ h1 ->
      B.live h1 o /\ B.live h1 i /\ B.modifies (B.loc_buffer o) h0 h1 /\
      as_seq h1 o == Seq.map f (ias_seq h0 i))
