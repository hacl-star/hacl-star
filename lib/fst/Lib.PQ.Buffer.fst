module Lib.PQ.Buffer

open FStar.HyperStack
open FStar.HyperStack.ST

open LowStar.Buffer

open Lib.IntTypes
open Lib.RawIntTypes

module B = LowStar.Buffer
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

module Seq = Lib.Sequence
module ByteSeq = Lib.ByteSequence

unfold let v = size_v

type lbuffer (a:Type0) (len:size_nat) = b:B.buffer a {B.length b == len}

val gsub:
    #a:Type0
  -> #len:size_nat
  -> #olen:size_nat
  -> b:lbuffer a len
  -> start:size_t
  -> n:size_t{v start + v n <= len /\ v n == olen}
  -> GTot (lbuffer a olen)
let gsub #a #len #olen b start n =
  B.gsub b (size_to_UInt32 start) (size_to_UInt32 n)

inline_for_extraction
val sub:
    #a:Type0
  -> #len:size_nat
  -> #olen:size_nat
  -> b:lbuffer a len
  -> start:size_t
  -> n:size_t{v start + v n <= len /\ v n == olen}
  -> Stack (lbuffer a olen)
    (requires fun h0 -> B.live h0 b)
    (ensures  fun h0 r h1 -> h0 == h1 /\ r == B.gsub b (size_to_UInt32 start) (size_to_UInt32 n))
let sub #a #len #olen b start n =
  B.sub b (size_to_UInt32 start) (size_to_UInt32 n)

inline_for_extraction
val index:
    #a:Type0
  -> #len:size_nat
  -> b:lbuffer a len
  -> i:size_t{v i < len}
  -> Stack a
    (requires fun h0 -> B.live h0 b)
    (ensures  fun h0 r h1 -> h0 == h1 /\ r == Seq.index #a #len (B.as_seq h1 b) (v i))
let index #a #len b i =
  B.index b (size_to_UInt32 i)

inline_for_extraction
val upd:
    #a:Type0
  -> #len:size_nat{len > 0}
  -> b:lbuffer a len
  -> i:size_t{v i < len}
  -> x:a
  -> Stack unit
    (requires fun h0 -> B.live h0 b)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer b) h0 h1 /\ B.live h1 b /\
      B.as_seq h1 b == Seq.upd #a #len (B.as_seq h0 b) (v i) x)
let upd #a #len b i v =
  B.upd b (size_to_UInt32 i) v

inline_for_extraction let op_Array_Assignment #a #len = upd #a #len
inline_for_extraction let op_Array_Access #a #len = index #a #len

unfold
let bget #a #n h (b:lbuffer a n) i = Seq.index #_ #n (B.as_seq h b) i

inline_for_extraction
val create:
    #a:Type0
  -> #len:size_nat
  -> clen:size_t{v clen == len}
  -> init:a
  -> StackInline (lbuffer a len)
    (requires fun h0 -> len > 0)
    (ensures  fun h0 b h1 ->
      B.alloc_post_mem_common b h0 h1 (Seq.create len init) /\
      frameOf b = HS.get_tip h0)
let create #a #len clen init =
  B.alloca init (normalize_term (size_to_UInt32 clen))

inline_for_extraction noextract
val createL:
    #a:Type0
  -> init:list a{List.Tot.length init <= max_size_t}
  -> StackInline (lbuffer a (normalize_term (List.Tot.length init)))
    (requires fun h0 -> B.alloca_of_list_pre #a init)
    (ensures fun h0 b h1 ->
      alloc_post_mem_common b h0 h1 (Seq.of_list init) /\
      frameOf b = HS.get_tip h0)
let createL #a init =
  B.alloca_of_list init

inline_for_extraction
val recall:
  #a:Type
  -> #len:size_nat
  -> b:lbuffer a len
  -> Stack unit
  (requires fun _ -> B.recallable b)
  (ensures  fun m0 _ m1 -> m0 == m1 /\ B.live m1 b)
let recall #a #len b = B.recall b

inline_for_extraction noextract
val createL_global:
    #a:Type0
  -> init:list a{List.Tot.length init <= max_size_t}
  -> ST (b:lbuffer a (normalize_term (List.Tot.length init)){
    frameOf b == HyperStack.root /\ recallable b})
    (requires fun h0 -> B.gcmalloc_of_list_pre #a HyperStack.root init)
    (ensures  fun h0 b h1 ->
      B.alloc_post_mem_common b h0 h1 (Seq.of_list init))
let createL_global #a init =
  B.gcmalloc_of_list HyperStack.root init

inline_for_extraction
val copy:
    #a:Type
  -> #len:size_nat
  -> o:lbuffer a len
  -> clen:size_t{v clen == len}
  -> i:lbuffer a len
  -> Stack unit
    (requires fun h0 -> B.live h0 o /\ B.live h0 i /\ B.disjoint i o)
    (ensures  fun h0 _ h1 ->
      B.live h1 o /\ B.live h1 i /\ modifies (loc_buffer o) h0 h1 /\
      B.as_seq h1 o == B.as_seq h0 i)
let copy #a #len o clen i =
  let h0 = ST.get () in
  LowStar.BufferOps.blit i (size_to_UInt32 (size 0)) o (size_to_UInt32 (size 0)) (size_to_UInt32 clen);
  let h1 = ST.get () in
  assert (Seq.slice #a #len (B.as_seq h1 o) 0 len == Seq.slice #a #len (B.as_seq h0 i) 0 len)

inline_for_extraction
val update_sub:
    #a:Type
  -> #len:size_nat
  -> dst:lbuffer a len
  -> start:size_t
  -> n:size_t{v start + v n <= len}
  -> src:lbuffer a (v n)
  -> Stack unit
    (requires fun h -> B.live h dst /\ B.live h src /\ B.disjoint dst src)
    (ensures  fun h0 _ h1 -> B.live h1 dst /\ modifies (loc_buffer dst) h0 h1 /\
      B.as_seq h1 dst == Seq.update_sub #a #len (B.as_seq h0 dst) (v start) (v n) (B.as_seq h0 src))
let update_sub #a #len dst start n src =
  let h0 = ST.get () in
  LowStar.BufferOps.blit src 0ul dst (size_to_UInt32 start) (size_to_UInt32 n);
  let h1 = ST.get () in
  assert (forall (k:nat{k < v n}). bget h1 dst (v start + k) == bget h0 src k);
  Seq.eq_intro
    (B.as_seq h1 dst)
    (Seq.update_sub #a #len (B.as_seq h0 dst) (v start) (v n) (B.as_seq h0 src))

(** Loop combinator with just memory safety specification *)
inline_for_extraction noextract
val loop_nospec:
    #h0:mem
  -> #a:Type0
  -> #len:size_nat
  -> n:size_t
  -> buf:lbuffer a len
  -> impl:
      (i:size_t{v i < v n} -> Stack unit
        (requires fun h -> modifies (loc_buffer buf) h0 h)
        (ensures  fun _ _ h1 -> modifies (loc_buffer buf) h0 h1))
  -> Stack unit
    (requires fun h -> h0 == h /\ B.live h0 buf)
    (ensures  fun _ _ h1 -> modifies (loc_buffer buf) h0 h1)
let loop_nospec #h0 #a #len n buf impl =
  let inv h1 j = modifies (loc_buffer buf) h0 h1 in
  Lib.Loops.for (size 0) n inv impl


(**
* A generalized loop combinator paremetrized by its state (e.g. an accumulator)
* 
* Arguments:
* - [h0] the heap when entering the loop. I couldn't factor it out because the specification of the body dedpends on it
* - [a_spec] the type for the specification state (may depend on the loop index)
* - [a_impl] the Low* type of the state (e.g a tuple of buffers)
* - [acc] Low* state
* - [refl] a ghost function that reflects the Low* state in an iteration as [a_spec]
* - [footprint] locations modified by the loop (may depend on the loop index)
* - [spec] a specification of how the body of the loop modifies the state
* - [impl] the body of the loop as a Stack function
*)
val loop_inv:
    h0:mem
  -> n:size_t
  -> a_spec:(i:size_nat{i <= v n} -> Type)
  -> a_impl:Type
  -> acc:a_impl
  -> refl:(mem -> i:size_nat{i <= v n} -> GTot (a_spec i))
  -> footprint:(i:size_nat{i <= v n} -> GTot loc)
  -> spec:(mem -> GTot (i:size_nat{i < v n} -> a_spec i -> a_spec (i + 1)))
  -> i:size_nat{i <= v n}
  -> h:mem 
  -> Type0
let loop_inv h0 n a_spec a_impl acc refl footprint spec i h =
  modifies (footprint i) h0 h /\
  refl h i == Seq.repeat i a_spec (spec h0) (refl h0 0)

inline_for_extraction noextract
val loop:
    h0:mem
  -> n:size_t
  -> a_spec:(i:size_nat{i <= v n} -> Type)
  -> a_impl:Type
  -> acc:a_impl
  -> refl:(mem -> i:size_nat{i <= v n} -> GTot (a_spec i))
  -> footprint:(i:size_nat{i <= v n} -> GTot loc)
  -> spec:(mem -> GTot (i:size_nat{i < v n} -> a_spec i -> a_spec (i + 1)))
  -> impl:(i:size_t{v i < v n} -> Stack unit
     (requires loop_inv h0 n a_spec a_impl acc refl footprint spec (v i))
     (ensures  fun _ _ -> loop_inv h0 n a_spec a_impl acc refl footprint spec (v i + 1)))
  -> Stack unit
    (requires fun h -> h0 == h)
    (ensures  fun _ _ -> loop_inv h0 n a_spec a_impl acc refl footprint spec (v n))
let loop h0 n a_spec a_impl acc refl footprint spec impl =
  let inv h i = loop_inv h0 n a_spec a_impl acc refl footprint spec i h in
  Lib.Loops.for (size 0) n inv impl

(** Compares two byte buffers of equal length returning a bool *)
inline_for_extraction
val lbytes_eq:
    #len:size_t
  -> a:lbuffer uint8 (v len)
  -> b:lbuffer uint8 (v len)
  -> Stack bool
    (requires fun h -> live h a /\ live h b)
    (ensures  fun h0 r h1 ->
      modifies loc_none h0 h1 /\
      r == Seq.lbytes_eq #(v len) (as_seq h0 a) (as_seq h0 b))
let lbytes_eq #len a b =
  push_frame();
  let res = create (size 1) true in
  [@ inline_let]
  let refl h _ = get h res 0 in
  [@ inline_let]
  let spec h0 = Seq.lbytes_eq_inner #(v len) (as_seq h0 a) (as_seq h0 b) in
  let h0 = ST.get () in
  loop h0 len (fun _ -> bool) (lbuffer bool 1) res refl 
    (fun i -> loc_buffer res) spec
    (fun i ->
      let ai = a.(i) in
      let bi = b.(i) in
      let res0 = res.(size 0) in
      res.(size 0) <- res0 && FStar.UInt8.(u8_to_UInt8 ai =^ u8_to_UInt8 bi)
    );
  let res = res.(size 0) in
  pop_frame();
  // REMARK: for some reason [lbytes_eq] isn't unfolded
  assert_norm ( 
    Seq.lbytes_eq #(v len) (as_seq h0 a) (as_seq h0 b) ==
    Seq.repeat (v len) (fun _ -> bool) (spec h0) true);
  res

// TODO: used in tests; move to a different module
assume 
val print_compare_display:
    len:size_t
  -> lbuffer uint8 (size_v len)
  -> lbuffer uint8 (size_v len)
  -> Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> h0 == h1)
