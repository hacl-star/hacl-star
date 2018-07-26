module Lib.PQ.Buffer

open FStar.HyperStack
open FStar.HyperStack.ST

open LowStar.ModifiesPat
open LowStar.Modifies

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
      B.modifies_1 b h0 h1 /\ B.live h1 b /\
      B.as_seq h1 b == Seq.upd #a #len (B.as_seq h0 b) (v i) x)
let upd #a #len b i v =
  B.upd b (size_to_UInt32 i) v

inline_for_extraction let op_Array_Assignment #a #len = upd #a #len
inline_for_extraction let op_Array_Access #a #len = index #a #len

inline_for_extraction
val create:
    #a:Type0
  -> #len:size_nat{len > 0}
  -> clen:size_t{v clen == len}
  -> init:a
  -> StackInline (lbuffer a len)
    (requires fun h0 -> True)
    (ensures  fun h0 r h1 ->
      B.alloc_post_common (HS.get_tip h0) len r h0 h1 /\
      B.as_seq h1 r == Seq.create len init)
let create #a #len clen init =
  B.alloca init (size_to_UInt32 clen)

inline_for_extraction
val createL:
    #a:Type0
  -> init:list a{List.Tot.length init <= max_size_t}
  -> StackInline (lbuffer a (List.Tot.length init))
    (requires fun h0 -> B.alloc_of_list_pre #a init)
    (ensures fun h0 r h1 ->
      let len = FStar.List.Tot.length init in
      B.alloc_post_common (HS.get_tip h0) len r h0 h1 /\
      B.as_seq h1 r == Seq.of_list init /\
      B.alloc_of_list_post #a len r)
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

inline_for_extraction
val createL_global:
    #a:Type0
  -> init:list a{List.Tot.length init <= max_size_t}
  -> ST (lbuffer a (List.Tot.length init))
    (requires fun h0 -> B.alloc_of_list_pre #a init)
    (ensures  fun h0 b h1 ->
      let len = FStar.List.Tot.length init in
      B.recallable b /\
      B.alloc_post_static HyperStack.root len b /\
      B.alloc_of_list_post len b /\
      B.alloc_post_common HyperStack.root len b h0 h1 /\
      B.as_seq h1 b == Seq.of_list init)
let createL_global #a init =
  B.gcmalloc_of_list HyperStack.root init


// val lemma_seq_slice_index:
//   #a:Type -> s1:Seq.seq a ->
//   s2:Seq.seq a{Seq.length s1 = Seq.length s2} ->
//   j:nat{j < Seq.length s1} -> Lemma
//   (requires ((Seq.slice s1 0 j == Seq.slice s2 0 j) /\ (Seq.index s1 j == Seq.index s2 j)))
//   (ensures  (Seq.slice s1 0 (j + 1) == Seq.slice s2 0 (j + 1)))
// let lemma_seq_slice_index #a s1 s2 j =
//   Seq.snoc_slice_index s1 0 j;
//   Seq.snoc_slice_index s2 0 j

// inline_for_extraction
// val copy:
//   #a:Type -> #len:size_nat ->
//   o:lbuffer a len -> clen:size_t{v clen == len} ->
//   i:lbuffer a len -> Stack unit
//   (requires (fun h0 -> B.live h0 o /\ B.live h0 i /\ B.disjoint i o))
//   (ensures (fun h0 _ h1 ->
//     B.live h1 o /\ B.live h1 i /\ modifies (loc_buffer o) h0 h1 /\
//     B.as_seq h1 o == B.as_seq h0 i))
// let copy #a #len o clen i =
//   let h0 = ST.get() in
//   let inv (h1:mem) (j:nat{j <= len}) =
//     B.live h1 o /\ B.live h1 i /\
//     modifies (loc_buffer o) h0 h1 /\
//     Seq.slice (B.as_seq h1 o) 0 j == Seq.slice (B.as_seq h0 i) 0 j in
//   let f' (j:size_t{0 <= v j /\ v j < len}) : Stack unit
//       (requires (fun h -> inv h (v j)))
//       (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
//       let h1 = ST.get () in
//       let src_i = i.(j) in
//       o.(j) <- src_i;
//       let h2 = ST.get () in
//       lemma_seq_slice_index (B.as_seq h2 o) (B.as_seq h0 i) (v j);
//       modifies_trans (loc_buffer o) h0 h1 (loc_buffer o) h2 in
//   Lib.Loops.for (size 0) clen inv f'

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
  -> start:size_t{v start < len}
  -> n:size_t{v start + v n <= len}
  -> src:lbuffer a (v n)
  -> Stack unit
    (requires fun h -> B.live h dst /\ B.live h src /\ B.disjoint dst src)
    (ensures  fun h0 _ h1 -> B.live h1 dst /\ modifies (loc_buffer dst) h0 h1 /\
      B.as_seq h1 dst == Seq.update_sub #a #len (B.as_seq h0 dst) (v start) (v n) (B.as_seq h0 src))
let update_sub #a #len dst start n src =
  let h0 = ST.get () in
  let b = sub dst start n in
  copy b n src;
  let h1 = ST.get () in

  assert (B.as_seq h1 b == B.as_seq h0 src);
  assert (forall (k:size_nat{0 <= k /\ k < v n}). Seq.index #_ #(v n) (B.as_seq h1 b) k == Seq.index #_ #(v n) (B.as_seq h0 src) k);
  assert (forall (k:size_nat{0 <= k /\ k < v start /\ v start + v n <= k /\ k < len}). Seq.index #_ #len (B.as_seq h1 dst) k == Seq.index #_ #len (B.as_seq h0 dst) k);

  assert (forall (k:size_nat{0 <= k /\ k < v start /\ v start + v n <= k /\ k < len}). Seq.index #_ #len (B.as_seq h1 dst) k ==
    Seq.index (Seq.update_sub #a #len (B.as_seq h0 dst) (v start) (v n) (B.as_seq h0 src)) k);
  assert (forall (k:size_nat{v start <= k /\ k < v start + v n}). Seq.index #_ #len (B.as_seq h1 dst) k ==
    Seq.index (Seq.update_sub #a #len (B.as_seq h0 dst) (v start) (v n) (B.as_seq h0 src)) k);

  assume (forall (k:size_nat{0 <= k /\ k < len}). Seq.index #_ #len (B.as_seq h1 dst) k ==
    Seq.index (Seq.update_sub #a #len (B.as_seq h0 dst) (v start) (v n) (B.as_seq h0 src)) k); //FIXME

  Seq.eq_intro (B.as_seq h1 dst) (Seq.update_sub #a #len (B.as_seq h0 dst) (v start) (v n) (B.as_seq h0 src))

inline_for_extraction noextract private
val loop_nospec_inv:
    #a:Type
  -> h0:mem
  -> h1:mem
  -> len:size_nat
  -> n:size_nat
  -> buf:lbuffer a len
  -> i:size_nat{i <= n}
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
  let inv h1 (j:nat{j <= v n}) =
    loop_nospec_inv #a h0 h1 len (v n) buf j in
  let f' (j:size_t{0 <= v j /\ v j < v n}): Stack unit
      (requires fun h -> inv h (v j))
      (ensures  fun _ _ h2 -> inv h2 (v j + 1)) =
      impl j in
  Lib.Loops.for (size 0) n inv f'


inline_for_extraction
val uint_from_bytes_le:
    #t:m_inttype{~(SIZE? t)}
  -> i:lbuffer uint8 (numbytes t)
  -> Stack (uint_t t)
    (requires fun h0 -> B.live h0 i)
    (ensures  fun h0 o h1 ->
      h0 == h1 /\ B.live h1 i /\
      o == ByteSeq.uint_from_bytes_le #t (B.as_seq h0 i))
let uint_from_bytes_le #t i =
  match t with
  | U8 -> i.(size 0)
  | U16 -> let u = C.load16_le i in u16_from_UInt16 u
  | U32 -> let u = C.load32_le i in u32_from_UInt32 u
  | U64 -> let u = C.load64_le i in u64_from_UInt64 u
  | U128 -> let u = C.load128_le i in u128_from_UInt128 u

inline_for_extraction
val uint_from_bytes_be:
    #t:m_inttype{~(SIZE? t)}
  -> i:lbuffer uint8 (numbytes t)
  -> Stack (uint_t t)
    (requires fun h0 -> B.live h0 i)
    (ensures  fun h0 o h1 ->
      h0 == h1 /\ B.live h1 i /\
      o == ByteSeq.uint_from_bytes_be #t (B.as_seq h0 i))
let uint_from_bytes_be #t i =
  match t with
  | U8 -> i.(size 0)
  | U16 -> let u = C.load16_be i in u16_from_UInt16 u
  | U32 -> let u = C.load32_be i in u32_from_UInt32 u
  | U64 -> let u = C.load64_be i in u64_from_UInt64 u
  | U128 -> let u = C.load128_be i in u128_from_UInt128 u

inline_for_extraction
val uint_to_bytes_le:
    #t:m_inttype{~(SIZE? t)}
  -> o:lbuffer uint8 (numbytes t)
  -> i:uint_t t
  -> Stack unit
    (requires fun h0 -> B.live h0 o)
    (ensures  fun h0 _ h1 ->
      B.live h1 o /\ modifies (loc_buffer o) h0 h1 /\
      B.as_seq h1 o == ByteSeq.uint_to_bytes_le #t i)
let uint_to_bytes_le #t o i =
  match t with
  | U8 -> o.(size 0) <- i
  | U16 -> C.store16_le o (u16_to_UInt16 i)
  | U32 -> C.store32_le o (u32_to_UInt32 i)
  | U64 -> C.store64_le o (u64_to_UInt64 i)
  | U128 -> C.store128_le o (u128_to_UInt128 i)

inline_for_extraction
val uint_to_bytes_be:
    #t:m_inttype{~(SIZE? t)}
  -> o:lbuffer uint8 (numbytes t)
  -> i:uint_t t
  -> Stack unit
    (requires fun h0 -> B.live h0 o)
    (ensures  fun h0 _ h1 ->
      B.live h1 o /\ modifies (loc_buffer o) h0 h1 /\
      B.as_seq h1 o == ByteSeq.uint_to_bytes_be #t i)
let uint_to_bytes_be #t o i =
  match t with
  | U8 -> o.(size 0) <- i
  | U16 -> C.store16_be o (u16_to_UInt16 i)
  | U32 -> C.store32_be o (u32_to_UInt32 i)
  | U64 -> C.store64_be o (u64_to_UInt64 i)
  | U128 -> C.store128_be o (u128_to_UInt128 i)

assume val print_compare_display:
    len:size_t
  -> lbuffer uint8 (size_v len)
  -> lbuffer uint8 (size_v len)
  -> Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)
