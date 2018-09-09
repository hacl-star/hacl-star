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

inline_for_extraction noextract private
val loop_nospec_inv:
    #a:Type
  -> h0:mem
  -> h1:mem
  -> len:size_nat
  -> n:size_nat
  -> buf:lbuffer a len
  -> i:nat
  -> Type0
let loop_nospec_inv #a h0 h1 len n buf i =
  B.live h0 buf /\ B.live h1 buf /\ modifies (loc_buffer buf) h0 h1

inline_for_extraction
val loop_nospec:
    #h0:mem
  -> #a:Type0
  -> #len:size_nat
  -> n:size_t
  -> buf:lbuffer a len
  -> impl:
      (i:size_t{v i < v n} -> Stack unit
        (requires fun h -> loop_nospec_inv #a h0 h len (v n) buf (v i))
        (ensures  fun _ r h1 -> loop_nospec_inv #a h0 h1 len (v n) buf (v i + 1)))
  -> Stack unit
    (requires fun h -> h0 == h /\ B.live h0 buf)
    (ensures  fun _ _ h1 -> B.live h1 buf /\ modifies (loc_buffer buf) h0 h1)
let loop_nospec #h0 #a #len n buf impl =
  let inv h1 j =
    loop_nospec_inv #a h0 h1 len (v n) buf j in
  let f' (j:size_t{0 <= v j /\ v j < v n}): Stack unit
      (requires fun h -> inv h (v j))
      (ensures  fun _ _ h2 -> inv h2 (v j + 1)) =
      impl j in
  Lib.Loops.for (size 0) n inv f'

inline_for_extraction noextract
val eq_u8: a:uint8 -> b:uint8 -> Tot bool
let eq_u8 a b =
  let open FStar.UInt8 in
  let open Lib.RawIntTypes in
  u8_to_UInt8 a =^ u8_to_UInt8 b

inline_for_extraction
val lbytes_eq:
     #len:size_t
  -> a:lbuffer uint8 (v len)
  -> b:lbuffer uint8 (v len)
  -> Stack bool
    (requires fun h -> live h a /\ live h b)
    (ensures  fun h0 r h1 -> modifies loc_none h0 h1 /\
      r == Seq.lbytes_eq #(v len) (as_seq h0 a) (as_seq h0 b))
let lbytes_eq #len a b =
  push_frame();
  let res:lbuffer bool 1 = create (size 1) true in
  let h0 = ST.get () in
  Lib.Loops.for (size 0) len
  (fun h1 i ->
    B.live h1 res /\ modifies (loc_buffer res) h0 h1 /\
    B.get h1 res 0 == Seq.lbytes_eq_fc #(v len) (as_seq h0 a) (as_seq h0 b) i)
  (fun i ->
    let a1 = res.(size 0) in
    let a2 = eq_u8 a.(i) b.(i) in
    res.(size 0) <- a1 && a2
  );
  let res = res.(size 0) in
  pop_frame();
  res

// TODO: move to a different module
assume val print_compare_display:
    len:size_t
  -> lbuffer uint8 (size_v len)
  -> lbuffer uint8 (size_v len)
  -> Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> h0 == h1)
