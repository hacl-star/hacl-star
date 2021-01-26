module Lib.Buffer

open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.RawIntTypes

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module CB = LowStar.ConstBuffer
module LMB = LowStar.Monotonic.Buffer

module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

module Seq = Lib.Sequence
module ByteSeq = Lib.ByteSequence
module Loop = Lib.LoopCombinators

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 1"

type buftype =
  | MUT
  | IMMUT
  | CONST

inline_for_extraction
let buffer_t (ty:buftype) (a:Type0) =
  match ty with
  | IMMUT -> IB.ibuffer a
  | MUT -> B.buffer a
  | CONST -> CB.const_buffer a

(** Mutable buffer. Extracted as `a*` *)
unfold let buffer (a:Type0) = buffer_t MUT a

(** Immutable buffer. Extracted as `a*`. Enjoys nice properties for recalling contents. *)
unfold let ibuffer (a:Type0) = buffer_t IMMUT a

(** Const buffer. Either one of the two above. Extracts as `const a*`. *)
unfold let cbuffer (a:Type0) = buffer_t CONST a

(** Global buffers are const immutable *)
unfold let gbuffer (a:Type0) = c:cbuffer a{CB.qual_of c == CB.IMMUTABLE}

let length (#t:buftype) (#a:Type0) (b:buffer_t t a) =
  match t with
  | MUT -> B.length (b <: buffer a)
  | IMMUT -> IB.length (b <: ibuffer a)
  | CONST -> CB.length (b <: cbuffer a)

let to_const #a #t (b:buffer_t t a) : r:cbuffer a {length r == length b}=
  match t with
  | MUT -> CB.of_buffer (b <: buffer a)
  | IMMUT -> CB.of_ibuffer (b <: ibuffer a)
  | CONST -> b <: cbuffer a

let const_to_buffer #a (b:cbuffer a{CB.qual_of b == CB.MUTABLE}) : r:buffer a{length r == length b} =
  CB.to_buffer b

let const_to_ibuffer #a (b:cbuffer a{CB.qual_of b == CB.IMMUTABLE}) : r:ibuffer a{length r == length b} =
  CB.to_ibuffer b


inline_for_extraction
let lbuffer_t (ty:buftype) (a:Type0) (len:size_t) =
  b:buffer_t ty a{length #ty #a b == v len}

unfold let lbuffer (a:Type0) (len:size_t) = lbuffer_t MUT a len
unfold let ilbuffer (a:Type0) (len:size_t) = lbuffer_t IMMUT a len
unfold let clbuffer (a:Type0) (len:size_t) = lbuffer_t CONST a len
unfold let glbuffer (a:Type0) (len:size_t) = c:clbuffer a len{CB.qual_of #a c == CB.IMMUTABLE}

let const_to_lbuffer #a #len (b:clbuffer a len{CB.qual_of (b <: cbuffer a) == CB.MUTABLE}) : r:lbuffer a len =
  const_to_buffer #a b

let const_to_ilbuffer #a #len (b:glbuffer a len)  : r:ilbuffer a len =
  const_to_ibuffer #a b

unfold let null (a: Type0) : lbuffer a (size 0) = B.null #a

//val live: #t:buftype -> #a:Type0 -> h:HS.mem -> b:buffer_t t a -> Type
let live (#t:buftype) (#a:Type0) (h:HS.mem) (b:buffer_t t a) : Type =
  match t with
  | MUT -> B.live h (b <: buffer a)
  | IMMUT -> IB.live h (b <: ibuffer a)
  | CONST -> CB.live h (b <: cbuffer a)

let loc (#t:buftype) (#a:Type0) (b:buffer_t t a) : GTot B.loc =
  match t with
  | MUT -> B.loc_buffer (b <: buffer a)
  | IMMUT -> B.loc_buffer (b <: ibuffer a)
  | CONST -> CB.loc_buffer (b <: cbuffer a)

#set-options "--max_ifuel 0"

let union (l1:B.loc) (l2:B.loc) : GTot B.loc = B.loc_union l1 l2
let ( |+| ) (l1:B.loc) (l2:B.loc) : GTot B.loc = union l1 l2

(** Generalized modification clause for Buffer locations *)
let modifies (s:B.loc) (h1 h2:HS.mem) = B.modifies s h1 h2

(* JP: redefining is generally dangerous; someone may inadvertently write a pattern
   for the disjoint predicate below, which does not enjoy transitivity, etc. and run
   into strange behavior. This explains why the SMTPat on mut_immut_disjoint
   operates over B.loc_disjoint, not disjoint. *)

(** Disjointness clause for Buffers *)
let disjoint (#t1 #t2:buftype) (#a1 #a2:Type0) (b1:buffer_t t1 a1) (b2:buffer_t t2 a2) =
  B.loc_disjoint (loc b1) (loc b2)

let mut_immut_disjoint #t #t' (b: buffer_t MUT t) (ib: buffer_t IMMUT t') (h: HS.mem):
  Lemma
    (requires (B.live h b /\ B.live h ib))
    (ensures (disjoint b ib))
    [SMTPat (B.loc_disjoint (loc b) (loc ib)); SMTPat (B.live h b); SMTPat (B.live h ib)]
=
  IB.buffer_immutable_buffer_disjoint b ib h

let mut_const_immut_disjoint #t #t' (b: buffer_t MUT t) (ib: buffer_t CONST t') (h: HS.mem):
  Lemma
    (requires (B.live h b /\ B.live h (CB.as_mbuf ib) /\ CB.qual_of #t' ib == CB.IMMUTABLE))
    (ensures (B.loc_disjoint (loc b) (loc ib)))
    [SMTPat (B.loc_disjoint (loc b) (loc ib)); SMTPat (B.live h b); SMTPat (B.live h (CB.as_mbuf ib))]
=
  IB.buffer_immutable_buffer_disjoint #t #t' b (CB.as_mbuf #t' ib) h

(** Modifies nothing *)
let modifies0 (h1 h2:HS.mem) =
  modifies (B.loc_none) h1 h2

(** Modifies one buffer *)
let modifies1 (#a:Type0) (b:buffer_t MUT a) (h1 h2:HS.mem) =
  modifies (loc b) h1 h2

(** Modifies two buffers *)
let modifies2 (#a0:Type0) (#a1:Type0)
  (b0:buffer_t MUT a0) (b1:buffer_t MUT a1) (h1 h2: HS.mem) =
  modifies (loc b0 |+| loc b1) h1 h2

(** Modifies three buffers *)
let modifies3 (#a0:Type0) (#a1:Type0) (#a2:Type0)
  (b0:buffer_t MUT a0) (b1:buffer_t MUT a1) (b2:buffer_t MUT a2) (h1 h2: HS.mem) =
  modifies (loc b0 |+| loc b1 |+| loc b2) h1 h2

(** Modifies four buffers *)
let modifies4 (#a0:Type0) (#a1:Type0) (#a2:Type0) (#a3:Type0)
  (b0:buffer_t MUT a0) (b1:buffer_t MUT a1) (b2:buffer_t MUT a2) (b3:buffer_t MUT a3)
  (h1 h2: HS.mem) =
  modifies (loc b0 |+| loc b1 |+| loc b2 |+| loc b3) h1 h2

(** Modifies five buffers *)
let modifies5 (#a0:Type0) (#a1:Type0) (#a2:Type0) (#a3:Type0) (#a4:Type0)
  (b0:buffer_t MUT a0) (b1:buffer_t MUT a1) (b2:buffer_t MUT a2) (b3:buffer_t MUT a3)
  (b4:buffer_t MUT a4) (h1 h2: HS.mem) =
  modifies (loc b0 |+| loc b1 |+| loc b2 |+| loc b3 |+| loc b4) h1 h2

(** Modifies six buffers *)
let modifies6 (#a0:Type0) (#a1:Type0) (#a2:Type0) (#a3:Type0) (#a4:Type0) (#a5:Type0)
  (b0:buffer_t MUT a0) (b1:buffer_t MUT a1) (b2:buffer_t MUT a2) (b3:buffer_t MUT a3)
  (b4:buffer_t MUT a4) (b5:buffer_t MUT a5) (h1 h2: HS.mem) =
  modifies (loc b0 |+| loc b1 |+| loc b2 |+| loc b3 |+| loc b4 |+| loc b5) h1 h2

(** Ghost reveal a buffer as a sequence *)
let as_seq (#t:buftype) (#a:Type0) (#len:size_t) (h:HS.mem) (b:lbuffer_t t a len) :
  GTot (Seq.lseq a (v len)) =
  match t with
  | MUT -> B.as_seq h (b <: buffer a)
  | IMMUT -> IB.as_seq h (b <: ibuffer a)
  | CONST -> CB.as_seq h (b <: cbuffer a)

(** Ghostly get a sub-buffer of a buffer *)
let gsub (#t:buftype) (#a:Type0) (#len:size_t) (b:lbuffer_t t a len)
  (start:size_t) (n:size_t{v start + v n <= v len}) : GTot (lbuffer_t t a n)
=
  match t with
  | IMMUT->
    let b = IB.igsub (b <: ibuffer a) start n in
    assert (B.length b == v n);
    (b <: ilbuffer a n)
  | MUT ->
    let b = B.gsub (b <: buffer a) start n in
    assert (B.length b == v n);
    (b <: lbuffer a n)
  | CONST ->
    let b = CB.gsub (b <: cbuffer a) start n in
    assert (CB.length b == v n);
    (b <: clbuffer a n)

(** JP: are these not covered already by standard SMT patterns? is this to avoid
    having to invert on `buftype`? *)
val live_sub: #t:buftype -> #a:Type0 -> #len:size_t -> b:lbuffer_t t a len
  -> start:size_t -> n:size_t{v start + v n <= v len} -> h:mem
  -> Lemma
    (ensures live h b ==> live h (gsub b start n))
    [SMTPat (live h (gsub b start n))]

val modifies_sub: #t:buftype -> #a:Type0 -> #len:size_t -> b:lbuffer_t t a len
  -> start:size_t -> n:size_t{v start + v n <= v len} -> h0:mem -> h1:mem
  -> Lemma
    (requires modifies (loc (gsub b start n)) h0 h1)
    (ensures  modifies (loc b) h0 h1)
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

(** Statefully get a sub-buffer of a buffer *)
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

(** Statefully read an element in a buffer *)
inline_for_extraction
val index:
    #t:buftype
  -> #a:Type0
  -> #len:size_t{v len > 0}
  -> b:lbuffer_t t a len
  -> i:size_t{v i < v len} ->
  Stack a
    (requires fun h0 -> live h0 b)
    (ensures  fun h0 r h1 ->
      h0 == h1 /\
      r == Seq.index #a #(v len) (as_seq h1 b) (v i))

(** Update a specific value in a mutable buffer *)
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
      modifies1 b h0 h1 /\
      as_seq h1 b == Seq.upd #a #(v len) (as_seq h0 b) (v i) x)

(** Operator for updating a mutable buffer: b.(i) <- x *)
inline_for_extraction
let op_Array_Assignment #a #len = upd #a #len

(** Operator for accessing a buffer: b.(i) *)
inline_for_extraction
let op_Array_Access #t #a #len = index #t #a #len

(* 2018.16.11 SZ: this doesn't parse: let f a len (b:lbuffer a len) h = h.[| b |] *)
(** Operator for getting a ghost view of a buffer as a sequence: h.[(b)] *)
inline_for_extraction
let op_Brack_Lens_Access #t #a #len = as_seq #t #a #len

(** Ghostly read an element in a buffer *)
let bget (#t:buftype) (#a:Type0) (#len:size_t) (h:mem) (b:lbuffer_t t a len)
  (i:size_nat{i < v len}) : GTot a
=
  match t with
  | MUT -> B.get h (b <: buffer a) i
  | IMMUT -> IB.get h (b <: ibuffer a) i
  | CONST -> FStar.Seq.index (CB.as_seq h (b <: cbuffer a)) i

(* We don't have access to Lib.Sequence to know `Lib.Sequence.index == FStar.Seq.index` *)
val bget_as_seq:
    #t:buftype
  -> #a:Type0
  -> #len:size_t
  -> h:mem
  -> b:lbuffer_t t a len
  -> i:size_nat
  -> Lemma
    (requires i < v len)
    (ensures  bget #t #a #len h b i == Seq.index #a #(v len) (as_seq h b) i)
    [SMTPat (bget #t #a #len h b i)]

let stack_allocated (#a:Type0) (#len:size_t) (b:lbuffer a len)
                    (h0:mem) (h1:mem) (s:Seq.lseq a (v len)) =
  let b: B.buffer a = b in
  B.alloc_post_mem_common b h0 h1 s /\
  B.frameOf b = HS.get_tip h0 /\
  B.frameOf b <> HyperStack.root

let global_allocated (#a:Type0) (#len:size_t) (b:glbuffer a len)
                    (h0:mem) (h1:mem) (s:Seq.lseq a (v len)) =
  let b: ibuffer a = CB.as_mbuf b in
  B.frameOf b == HyperStack.root /\
  B.alloc_post_mem_common b h0 h1 s

let recallable (#t:buftype) (#a:Type0) (#len:size_t) (b:lbuffer_t t a len) =
  match t with
  | IMMUT ->  B.recallable (b <: ibuffer a)
  | MUT -> B.recallable (b <: buffer a)
  | CONST -> B.recallable (CB.as_mbuf (b <: cbuffer a))

inline_for_extraction 
val recall:
    #t:buftype 
  -> #a:Type0
  -> #len:size_t
  -> b:lbuffer_t t a len -> 
  Stack unit
    (requires fun _ -> recallable b)
    (ensures  fun h0 _ h1 -> h0 == h1 /\ live h0 b)

unfold private
let cpred (#a:Type0) (s:Seq.seq a) : B.spred a = fun s1 -> FStar.Seq.equal s s1

let witnessed (#a:Type0) (#len:size_t) (b:glbuffer a len) (s:Seq.lseq a (v len)) =
  B.witnessed (CB.as_mbuf b) (cpred s)

(** Allocate a stack fixed-length mutable buffer and initialize it to value [init] *)
inline_for_extraction
val create:
    #a:Type0
  -> len:size_t
  -> init:a ->
  StackInline (lbuffer a len)
    (requires fun h0 -> v len > 0)
    (ensures  fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 (Seq.create (v len) init))

#set-options "--max_fuel 1"

(** Allocate a stack fixed-length mutable buffer initialized to a list *)
inline_for_extraction 
val createL:
    #a:Type0
  -> init:list a{normalize (List.Tot.length init <= max_size_t)} ->
  StackInline (lbuffer a (size (normalize_term (List.Tot.length init))))
    (requires fun h0 -> B.alloca_of_list_pre #a init)
    (ensures  fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 (Seq.of_list init))

(** Allocate a global fixed-length const immutable buffer initialized to value [init] *)
inline_for_extraction 
val createL_global:
    #a:Type0
  -> init:list a{normalize (List.Tot.length init <= max_size_t)} ->
  ST (glbuffer a (size (normalize_term (List.Tot.length init))))
    (requires fun h0 -> B.gcmalloc_of_list_pre #a HyperStack.root init)
    (ensures  fun h0 b h1 -> global_allocated b h0 h1 (Seq.of_list init) /\
                          recallable b /\
                          witnessed b (Seq.of_list init))

#set-options "--max_fuel 0"

(** Recall the liveness and contents of a global immutable buffer *)
inline_for_extraction 
val recall_contents:
    #a:Type0
  -> #len:size_t{v len <= max_size_t}
  -> b:glbuffer a len
  -> s:Seq.lseq a (v len) ->
  ST unit
    (requires fun h0 -> (live h0 b \/ recallable b) /\ witnessed b s)
    (ensures  fun h0 _ h1 -> h0 == h1 /\ live h0 b /\ as_seq h0 b == s)

(** Copy a buffer into a mutable buffer *)
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
      modifies1 o h0 h1 /\
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

(** Copy a buffer into a sub-buffer of a mutable buffer *)
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
    (ensures  fun h0 _ h1 ->
      modifies1 dst h0 h1 /\
      as_seq h1 dst == Seq.update_sub (as_seq h0 dst) (v start) (v n) (as_seq h0 src))

(** Update a mutable buffer in-place by applying a function on a sub-buffer of it *)
inline_for_extraction
val update_sub_f:
    #a:Type
  -> #len:size_t
  -> h0:mem
  -> buf:lbuffer a len
  -> start:size_t
  -> n:size_t{v start + v n <= v len}
  -> spec:(mem -> GTot (Seq.lseq a (v n)))
  -> f:(unit -> Stack unit
      (requires fun h -> h0 == h)
      (ensures  fun h0 _ h1 ->
       (let b = gsub buf start n in
       modifies (loc b) h0 h1 /\
       as_seq h1 b == spec h0))) ->
  Stack unit
    (requires fun h -> h0 == h /\ live h buf)
    (ensures  fun h0 _ h1 ->
      modifies (loc buf) h0 h1 /\
      as_seq h1 buf == Seq.update_sub #a #(v len) (as_seq h0 buf) (v start) (v n) (spec h0))

(** Copy two buffers one after the other into a mutable buffer *)
inline_for_extraction
val concat2:
    #t0:buftype
  -> #t1:buftype
  -> #a:Type0
  -> len0:size_t
  -> s0:lbuffer_t t0 a len0
  -> len1:size_t{v len0 + v len1 <= max_size_t}
  -> s1:lbuffer_t t1 a len1
  -> s:lbuffer a (len0 +! len1)
  -> Stack unit
    (requires fun h ->
      live h s0 /\ live h s1 /\ live h s /\
      disjoint s s0 /\ disjoint s s1)
    (ensures fun h0 _ h1 ->
      modifies1 s h0 h1 /\
      as_seq h1 s == Seq.concat (as_seq h0 s0) (as_seq h0 s1))

(** Copy three buffers one after the other into a mutable buffer *)
inline_for_extraction
val concat3:
    #t0:buftype
  -> #t1:buftype
  -> #t2:buftype
  -> #a:Type0
  -> len0:size_t
  -> s0:lbuffer_t t0 a len0
  -> len1:size_t{v len0 + v len1 <= max_size_t}
  -> s1:lbuffer_t t1 a len1
  -> len2:size_t{v len0 + v len1 + v len2 <= max_size_t}
  -> s2:lbuffer_t t2 a len2
  -> s:lbuffer a (len0 +! len1 +! len2)
  -> Stack unit
    (requires fun h ->
      live h s0 /\ live h s1 /\ live h s2 /\ live h s /\
      disjoint s s0 /\ disjoint s s1 /\ disjoint s s2)
    (ensures fun h0 _ h1 ->
      modifies1 s h0 h1 /\
      as_seq h1 s == Seq.concat (Seq.concat (as_seq h0 s0) (as_seq h0 s1)) (as_seq h0 s2))

(** Loop combinator with just memory safety specification *)
inline_for_extraction 
val loop_nospec:
    #h0:mem
  -> #a:Type0
  -> #len:size_t
  -> n:size_t
  -> buf:lbuffer a len
  -> impl: (i:size_t{v i < v n} -> Stack unit
      (requires fun h -> modifies1 buf h0 h)
      (ensures  fun _ _ h1 -> modifies1 buf h0 h1)) ->
  Stack unit
    (requires fun h -> h0 == h /\ live h0 buf)
    (ensures  fun _ _ h1 -> modifies1 buf h0 h1)

(** Loop combinator with just memory safety specification *)
inline_for_extraction 
val loop_nospec2:
    #h0:mem
  -> #a1:Type0
  -> #a2:Type0
  -> #len1:size_t
  -> #len2:size_t
  -> n:size_t
  -> buf1:lbuffer a1 len1
  -> buf2:lbuffer a2 len2
  -> impl: (i:size_t{v i < v n} -> Stack unit
      (requires fun h -> modifies2 buf1 buf2 h0 h)
      (ensures  fun _ _ h1 -> modifies2 buf1 buf2 h0 h1)) ->
  Stack unit
    (requires fun h -> h0 == h /\ live h0 buf1 /\ live h0 buf2)
    (ensures  fun _ _ h1 -> modifies2 buf1 buf2 h0 h1)

(** Loop combinator with just memory safety specification *)
inline_for_extraction 
val loop_nospec3:
    #h0:mem
  -> #a1:Type0
  -> #a2:Type0
  -> #a3:Type0
  -> #len1:size_t
  -> #len2:size_t
  -> #len3:size_t
  -> n:size_t
  -> buf1:lbuffer a1 len1
  -> buf2:lbuffer a2 len2
  -> buf3:lbuffer a3 len3
  -> impl: (i:size_t{v i < v n} -> Stack unit
      (requires fun h -> modifies3 buf1 buf2 buf3 h0 h)
      (ensures  fun _ _ h1 -> modifies3 buf1 buf2 buf3 h0 h1)) ->
  Stack unit
    (requires fun h -> h0 == h /\ live h0 buf1 /\ live h0 buf2 /\ live h0 buf3)
    (ensures  fun _ _ h1 -> modifies3 buf1 buf2 buf3 h0 h1)

(** Loop combinator with just memory safety specification *)
inline_for_extraction 
val loop_range_nospec:
    #h0:mem
  -> #a:Type0
  -> #len:size_t
  -> start:size_t
  -> n:size_t{v start + v n <= max_size_t}
  -> buf:lbuffer a len
  -> impl: (i:size_t{v start <= v i /\ v i < v start + v n} -> Stack unit
      (requires fun h -> modifies1 buf h0 h)
      (ensures  fun _ _ h1 -> modifies1 buf h0 h1)) ->
  Stack unit
    (requires fun h -> h0 == h /\ live h0 buf)
    (ensures  fun _ _ h1 -> modifies1 buf h0 h1)

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

(**
* A generalized loop combinator paremetrized by its state (e.g. an accumulator)
*
* Arguments:
* - [h0] the heap when entering the loop
* - [n] the number of iterations
* - [a_spec] the type for the specification state (may depend on the loop index)
* - [refl] a ghost function that reflects the Low* state in an iteration as [a_spec]
* - [footprint] locations modified by the loop (may depend on the loop index)
* - [spec] a specification of how the body of the loop modifies the state
* - [impl] the body of the loop as a Stack function
*)
inline_for_extraction 
val loop:
    h0:mem
  -> n:size_t
  -> a_spec:(i:size_nat{i <= v n} -> Type)
  -> refl:(mem -> i:size_nat{i <= v n} -> GTot (a_spec i))
  -> footprint:(i:size_nat{i <= v n} -> GTot B.loc)
  -> spec:(mem -> GTot (i:size_nat{i < v n} -> a_spec i -> a_spec (i + 1)))
  -> impl:(i:size_t{v i < v n} -> Stack unit
      (requires loop_inv h0 n a_spec refl footprint spec (v i))
      (ensures  fun _ _ h -> loop_inv h0 n a_spec refl footprint spec (v i + 1) h)) ->
  Stack unit
    (requires fun h -> h0 == h)
    (ensures  fun h0 _ h1 -> loop_inv h0 n a_spec refl footprint spec (v n) h1)


let loop_refl_inv
  (h0:mem)
  (n:size_t)
  (a_spec: Type)
  (refl:(mem -> GTot a_spec))
  (footprint:B.loc)
  (spec:(mem -> GTot (i:size_nat{i < v n} -> a_spec -> a_spec)))
  (i:size_nat{i <= v n})
  (h:mem):
  Type0
=
  modifies footprint h0 h /\
  refl h == Loop.repeati i (spec h0) (refl h0)

inline_for_extraction 
val loop_refl:
    h0:mem
  -> n:size_t
  -> a_spec:Type
  -> refl:(mem -> GTot a_spec)
  -> footprint:Ghost.erased B.loc
  -> spec:(mem -> GTot (i:size_nat{i < v n} -> a_spec -> a_spec))
  -> impl:(i:size_t{v i < v n} -> Stack unit
      (requires loop_refl_inv h0 n a_spec refl footprint spec (v i))
      (ensures  fun _ _ h -> loop_refl_inv h0 n a_spec refl footprint spec (v i + 1) h)) ->
  Stack unit
    (requires fun h -> h0 == h)
    (ensures  fun h0 _ h1 -> loop_refl_inv h0 n a_spec refl footprint spec (v n) h1)

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
  modifies1 write h0 h /\
  as_seq h write == Loop.repeati i (spec h0) (as_seq h0 write)

(** Loop combinator specialized to modifying a single buffer [write] *)
inline_for_extraction 
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
  modifies2 write0 write1 h0 h /\
  (let s0, s1 = Loop.repeati i (spec h0) (as_seq h0 write0, as_seq h0 write1) in
   as_seq h write0 == s0 /\ as_seq h write1 == s1)

(** Loop combinator specialized to modifying two buffers [write0] and [write1] *)
inline_for_extraction 
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
* [spec] is the functional post-condition of [impl], it only takes the final memory
* because the initial memory is determined by [h]

* [spec_inv] is used to propagate the post-condition of [impl] to the final memory
* after popping the stack frame
*)
inline_for_extraction 
val salloc1_with_inv:
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
        B.modifies (B.loc_none) h h0 /\ ~(live_region h (get_tip h0)) /\
        B.frameOf b == get_tip h0 /\ B.live h0 b /\ B.as_seq h0 b == Seq.create (v len) x)
      (ensures  fun h0 r h1 ->
        B.modifies (B.loc_union (B.loc_all_regions_from false (get_tip h0))
                                (Ghost.reveal footprint)) h0 h1 /\
        spec r h1)) ->
  Stack res
    (requires fun h0 -> h0 == h)
    (ensures  fun h0 r h1 -> modifies (Ghost.reveal footprint) h0 h1 /\ spec r h1)

inline_for_extraction 
val salloc1:
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

inline_for_extraction 
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
        B.modifies (B.loc_none) h h0 /\ ~(live_region h (get_tip h0)) /\
        B.frameOf b == get_tip h0 /\ B.live h0 b /\ B.as_seq h0 b == Seq.create (v len) x)
      (ensures  fun h0 r h1 ->
        B.modifies (B.loc_union (B.loc_all_regions_from false (get_tip h0))
                                (Ghost.reveal footprint)) h0 h1)) ->
  Stack res
    (requires fun h0 -> h0 == h)
    (ensures  fun h0 r h1 -> modifies (Ghost.reveal footprint) h0 h1)

inline_for_extraction 
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
            modifies1 w h0 h1 /\
            as_seq h1 w == spec_f (v i) (as_seq h0 inp) (as_seq h0 w)))
  -> l:(i:size_t{v i == v inpLen / v blocksize}
       -> len:size_t{v len == v inpLen % v blocksize}
       -> inp:lbuffer a len
       -> w:lbuffer b blen -> Stack unit
          (requires fun h ->
            live h inp /\ live h w /\ disjoint inp w)
          (ensures  fun h0 _ h1 ->
            modifies1 w h0 h1 /\
            as_seq h1 w == spec_l (v i) (v len) (as_seq h0 inp) (as_seq h0 w)))
  -> write:lbuffer b blen ->
  Stack unit
    (requires fun h -> live h inp /\ live h write /\ disjoint inp write)
    (ensures  fun h0 _ h1 ->
      modifies1 write h0 h1 /\
      as_seq h1 write ==
      Seq.repeati_blocks #a #(Seq.lseq b (v blen)) (v blocksize) (as_seq h0 inp) spec_f spec_l (as_seq h0 write))

inline_for_extraction 
val loopi_blocks_nospec:
    #a:Type0
  -> #b:Type0
  -> #blen:size_t
  -> blocksize:size_t{v blocksize > 0}
  -> inpLen:size_t
  -> inp:lbuffer a inpLen
  -> f:(i:size_t{v i < v inpLen / v blocksize}
       -> inp:lbuffer a blocksize
       -> w:lbuffer b blen -> Stack unit
          (requires fun h ->
            live h inp /\ live h w /\ B.loc_disjoint (loc inp) (loc w))
          (ensures  fun h0 _ h1 ->
            modifies1 w h0 h1))
  -> l:(i:size_t{v i == v inpLen / v blocksize}
       -> len:size_t{v len == v inpLen % v blocksize}
       -> inp:lbuffer a len
       -> w:lbuffer b blen -> Stack unit
          (requires fun h ->
            live h inp /\ live h w /\ B.loc_disjoint (loc inp) (loc w))
          (ensures  fun h0 _ h1 ->
            modifies1 w h0 h1))
  -> write:lbuffer b blen ->
  Stack unit
    (requires fun h -> live h inp /\ live h write /\ disjoint inp write)
    (ensures  fun h0 _ h1 -> modifies1 write h0 h1)

inline_for_extraction 
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
            modifies1 w h0 h1 /\
            as_seq h1 w == spec_f (as_seq h0 inp) (as_seq h0 w)))
  -> l:(len:size_t{v len == v inpLen % v blocksize}
       -> inp:lbuffer a len
       -> w:lbuffer b blen -> Stack unit
          (requires fun h ->
            live h inp /\ live h w /\ disjoint inp w)
          (ensures  fun h0 _ h1 ->
            modifies1 w h0 h1 /\
            as_seq h1 w == spec_l (v len) (as_seq h0 inp) (as_seq h0 w)))
  -> write:lbuffer b blen ->
  Stack unit
    (requires fun h -> live h inp /\ live h write /\ disjoint inp write)
    (ensures  fun h0 _ h1 ->
      modifies1 write h0 h1 /\
      as_seq h1 write ==
      Seq.repeat_blocks #a #(Seq.lseq b (v blen)) (v blocksize) (as_seq h0 inp) spec_f spec_l (as_seq h0 write))

open FStar.Mul
(*
(** Fills a buffer block by block using a function with an accumulator *)
inline_for_extraction 
val fill_blocks_:
    #t:Type0
  -> h0:mem
  -> len:size_t
  -> n:size_t{v n * v len <= max_size_t}
  -> output:lbuffer t (n *! len)
  -> a_spec:(i:size_nat{i <= v n} -> Type)
  -> refl:(mem -> i:size_nat{i <= v n} -> GTot (a_spec i))
  -> footprint:(i:size_nat{i <= v n} -> GTot
      (l:B.loc{B.loc_disjoint l (loc output) /\
               B.address_liveness_insensitive_locs `B.loc_includes` l}))
  -> spec:(mem -> GTot (i:size_nat{i < v n} -> a_spec i -> a_spec (i + 1) & Seq.lseq t (v len)))
  -> impl:(i:size_t{v i < v n} -> block:lbuffer t len -> Stack unit
      (requires fun h1 ->
        live h1 block /\
        loc output `B.loc_includes` loc block /\
        modifies (B.loc_union (footprint (v i)) (loc output)) h0 h1)
      (ensures  fun h1 _ h2 ->
        let s, b = spec h0 (v i) (refl h1 (v i)) in
        footprint (v i + 1) `B.loc_includes` footprint (v i) /\
        B.modifies (B.loc_union (footprint (v i + 1)) (loc block)) h1 h2 /\
        refl h2 (v i + 1) == s /\ as_seq h2 block == b)) ->
  Stack unit
    (requires fun h -> h0 == h /\ live h output)
    (ensures  fun _ _ h1 ->
      let s, o = Seq.generate_blocks (v len) (v n) a_spec (spec h0) (refl h0 0) in
      B.modifies (B.loc_union (footprint (v n)) (loc output)) h0 h1 /\
      refl h1 (v n) == s /\
      as_seq #_ #t h1 (gsub output (size 0) (n *! len)) == o)
*)

#set-options "--z3rlimit 150"

(** Fills a buffer block by block using a function with an accumulator *)
inline_for_extraction 
val fill_blocks:
    #t:Type0
  -> h0:mem
  -> len:size_t
  -> n:size_t{v n * v len <= max_size_t}
  -> output:lbuffer t (n *! len)
  -> a_spec:(i:size_nat{i <= v n} -> Type)
  -> refl:(mem -> i:size_nat{i <= v n} -> GTot (a_spec i))
  -> footprint:(i:size_nat{i <= v n} -> GTot
      (l:B.loc{B.loc_disjoint l (loc output) /\
               B.address_liveness_insensitive_locs `B.loc_includes` l}))
  -> spec:(mem -> GTot (i:size_nat{i < v n} -> a_spec i -> a_spec (i + 1) & Seq.lseq t (v len)))
  -> impl:(i:size_t{v i < v n} -> Stack unit
      (requires fun h1 ->
      	(v i + 1) * v len <= max_size_t /\
        modifies (footprint (v i) |+| loc (gsub output 0ul (i *! len))) h0 h1)
      (ensures  fun h1 _ h2 ->
        (let block = gsub output (i *! len) len in
        let s, b = spec h0 (v i) (refl h1 (v i)) in
        footprint (v i + 1) `B.loc_includes` footprint (v i) /\
        B.modifies (B.loc_union (footprint (v i + 1)) (loc block)) h1 h2 /\
        refl h2 (v i + 1) == s /\ as_seq h2 block == b))) ->
  Stack unit
    (requires fun h -> h0 == h /\ live h output)
    (ensures  fun _ _ h1 ->
      B.modifies (B.loc_union (footprint (v n)) (loc output)) h0 h1 /\
     (let s, o = Seq.generate_blocks (v len) (v n) (v n) a_spec (spec h0) (refl h0 0) in
      refl h1 (v n) == s /\
      as_seq #_ #t h1 output == o))

(** Fills a buffer block by block using a function without an accumulator *)
inline_for_extraction 
val fill_blocks_simple:
    #t:Type0
  -> h0:mem
  -> bs:size_t{v bs > 0}
  -> n:size_t{v bs * v n <= max_size_t}
  -> output:lbuffer t (bs *! n)
  -> spec:(mem -> GTot (i:size_nat{i < v n} -> Seq.lseq t (v bs)))
  -> impl:(i:size_t{v i < v n} -> Stack unit
      (requires fun h1 ->
        FStar.Math.Lemmas.lemma_mult_le_right (v bs) (v i) (v n);
      	(v i + 1) * v bs <= max_size_t /\
        modifies (loc (gsub output 0ul (i *! bs))) h0 h1)
      (ensures  fun h1 _ h2 ->
        (let block = gsub output (i *! bs) bs in
        let ob = spec h0 (v i) in
        B.modifies (loc block) h1 h2 /\
	as_seq h2 block == ob))) ->
  Stack unit
    (requires fun h -> h0 == h /\ live h output)
    (ensures  fun _ _ h1 -> modifies1 output h0 h1 /\
      as_seq #_ #t h1 output == Sequence.generate_blocks_simple (v bs) (v n) (v n) (spec h0))

(** Fill a buffer with a total function *)
inline_for_extraction
val fillT:
    #a:Type
  -> clen:size_t
  -> o:lbuffer a clen
  -> spec_f:(i:size_nat{i < v clen} -> a)
  -> f:(i:size_t{v i < v clen} -> r:a{r == spec_f (size_v i)}) ->
  Stack unit
    (requires fun h0 -> live h0 o)
    (ensures  fun h0 _ h1 ->
      modifies1 o h0 h1 /\
      as_seq h1 o == Seq.createi #a (v clen) spec_f)

(** Fill a buffer with a stateful function *)
inline_for_extraction
val fill:
    #a:Type
  -> h0:mem
  -> clen:size_t
  -> o:lbuffer a clen
  -> spec:(mem -> GTot(i:size_nat{i < v clen} -> a))
  -> impl:(i:size_t{v i < v clen} -> Stack a
          (requires fun h -> modifies1 (gsub o 0ul i) h0 h)
          (ensures  fun h r h' -> h == h' /\
			       r == spec h0 (v i)))
  -> Stack unit
    (requires fun h -> h == h0 /\ live h0 o)
    (ensures  fun h _ h' ->
      modifies1 o h h' /\
      as_seq h' o == Seq.createi #a (v clen) (spec h0))

inline_for_extraction 
let eq_or_disjoint
    (#t1:buftype)
    (#t2:buftype)
    (#a1:Type)
    (#a2:Type)
    (#clen1:size_t)
    (#clen2:size_t)
    (b1:lbuffer_t t1 a1 clen1)
    (b2:lbuffer_t t2 a2 clen2) =
    disjoint b1 b2 \/
    (t1 == t2 /\ a1 == a2 /\ clen1 == clen2 /\ b1 == b2)


(** Map a total function onto a buffer *)
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
    (requires fun h0 -> live h0 o /\ live h0 i /\ eq_or_disjoint o i)
    (ensures  fun h0 _ h1 ->
      modifies1 o h0 h1 /\
      as_seq h1 o == Seq.map f (as_seq h0 i))

inline_for_extraction
val map2T:
    #t:buftype
  -> #a1:Type
  -> #a2:Type
  -> #b:Type
  -> clen:size_t
  -> o:lbuffer b clen
  -> f:(a1 -> a2 -> Tot b)
  -> i1:lbuffer_t t a1 clen
  -> i2:lbuffer_t t a2 clen ->
  Stack unit
    (requires fun h0 -> live h0 o /\ live h0 i1 /\ live h0 i2 /\
		     eq_or_disjoint o i1 /\ eq_or_disjoint o i2)
    (ensures  fun h0 _ h1 ->
      modifies1 o h0 h1 /\
      as_seq h1 o == Seq.map2 f (as_seq h0 i1) (as_seq h0 i2))

(** Map a total function (depending on the index) onto a buffer *)
inline_for_extraction
val mapiT:
    #t:buftype
  -> #a:Type
  -> #b:Type
  -> clen:size_t
  -> o:lbuffer b clen
  -> f:(i:size_t{v i < v clen} -> x:a -> b)
  -> i:lbuffer_t t a clen ->
  Stack unit
    (requires fun h0 -> live h0 o /\ live h0 i /\ eq_or_disjoint o i)
    (ensures  fun h0 _ h1 ->
      modifies1 o h0 h1 /\
      as_seq h1 o == Seq.mapi (fun i -> f (size i)) (as_seq h0 i))

(** Map a stateful function with read effect onto a buffer *)
inline_for_extraction
val mapi:
    #a:Type
  -> #b:Type
  -> h0:mem
  -> clen:size_t
  -> o:lbuffer b clen
  -> spec_f:(mem -> GTot (i:size_nat{i < v clen} -> a -> b))
  -> f:(i:size_t{v i < v clen} -> x:a -> Stack b
      (requires fun h -> modifies1 o h0 h)
      (ensures  fun h y h1 -> h == h1 /\ y == spec_f h0 (v i) x))
  -> i:lbuffer a clen ->
  Stack unit
    (requires fun h -> h == h0 /\ live h0 o /\ live h0 i /\ eq_or_disjoint o i)
    (ensures  fun h _ h1 ->
      modifies1 o h h1 /\
      as_seq h1 o == Seq.mapi (spec_f h0) (as_seq h i))

inline_for_extraction 
val map_blocks_multi:
    #t:buftype
  -> #a:Type0
  -> h0: mem
  -> blocksize:size_t{v blocksize > 0}
  -> nb:size_t{v nb * v blocksize <= max_size_t}
  -> inp:lbuffer_t t a (nb *! blocksize)
  -> output:lbuffer a (nb *! blocksize)
  -> spec_f:(mem -> GTot (i:nat{i < v nb} -> Seq.lseq a (v blocksize) -> Seq.lseq a (v blocksize)))
  -> impl_f:(i:size_t{v i < v nb} -> Stack unit
      (requires fun h1 ->
        FStar.Math.Lemmas.lemma_mult_le_right (v blocksize) (v i) (v nb);
        (v i + 1) * v blocksize <= max_size_t /\
        modifies (loc (gsub output 0ul (i *! blocksize))) h0 h1)
      (ensures  fun h1 _ h2 ->
	let iblock = gsub inp (i *! blocksize) blocksize in
	let oblock = gsub output (i *! blocksize) blocksize in
        let ob = spec_f h0 (v i) (as_seq h1 iblock) in
        B.modifies (loc oblock) h1 h2 /\
        as_seq h2 oblock == ob))
  -> Stack unit
    (requires fun h -> h0 == h /\ live h output /\ live h inp /\ eq_or_disjoint inp output)
    (ensures  fun _ _ h1 -> modifies1 output h0 h1 /\
	as_seq h1 output == Seq.map_blocks_multi (v blocksize) (v nb) (v nb) (as_seq h0 inp) (spec_f h0))

inline_for_extraction 
val map_blocks:
    #t:buftype
  -> #a:Type0
  -> h0: mem
  -> len:size_t
  -> blocksize:size_t{v blocksize > 0}
  -> inp:lbuffer_t t a len
  -> output:lbuffer a len
  -> spec_f:(mem -> GTot (i:nat{i < v len / v blocksize} -> Seq.lseq a (v blocksize) -> Seq.lseq a (v blocksize)))
  -> spec_l:(mem -> GTot (i:nat{i == v len / v blocksize} -> llen:size_nat{llen < v blocksize} -> Seq.lseq a llen -> Seq.lseq a llen))
  -> impl_f:(i:size_t{v i < v len / v blocksize} -> Stack unit
      (requires fun h1 ->
        FStar.Math.Lemmas.lemma_mult_le_right (v blocksize) (v i) (v len / v blocksize);
        (v i + 1) * v blocksize <= max_size_t /\
        modifies (loc (gsub output 0ul (i *! blocksize))) h0 h1)
      (ensures  fun h1 _ h2 ->
	let iblock = gsub inp (i *! blocksize) blocksize in
	let oblock = gsub output (i *! blocksize) blocksize in
        let ob = spec_f h0 (v i) (as_seq h1 iblock) in
        B.modifies (loc oblock) h1 h2 /\
        as_seq h2 oblock == ob))
  -> impl_l:(i:size_t{v i == v len / v blocksize} -> Stack unit
      (requires fun h1 ->
        modifies (loc (gsub output 0ul (i *! blocksize))) h0 h1)
      (ensures  fun h1 _ h2 ->
	let iblock = gsub inp (i *! blocksize) (len %. blocksize)  in
	let oblock = gsub output (i *! blocksize) (len %. blocksize) in
        let ob = spec_l h0 (v i) (v len % v blocksize) (as_seq h1 iblock) in
        B.modifies (loc oblock) h1 h2 /\
        as_seq h2 oblock == ob))
  -> Stack unit
    (requires fun h -> h0 == h /\ live h output /\ live h inp /\ eq_or_disjoint inp output)
    (ensures  fun _ _ h1 -> modifies1 output h0 h1 /\
	as_seq h1 output == Seq.map_blocks (v blocksize) (as_seq h0 inp) (spec_f h0) (spec_l h0))

