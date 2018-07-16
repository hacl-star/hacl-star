module Lib.PQ.Buffer

open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.ModifiesPat
open LowStar.Modifies

module Buf = LowStar.Buffer
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

module Seq = FStar.Seq

open Lib.IntTypes
open Lib.RawIntTypes

unfold let v = size_v

type lbuffer (a:Type0) (len:size_nat) = b:Buf.buffer a {Buf.length b == len}

inline_for_extraction
val sub:
  #a:Type0 -> #len:size_nat -> #olen:size_nat ->
  b:lbuffer a len -> start:size_t ->
  n:size_t{v start + v n <= len /\ v n == olen} -> Stack (lbuffer a olen)
  (requires (fun h0 -> Buf.live h0 b))
  (ensures (fun h0 r h1 -> h0 == h1 /\ r == Buf.gsub b (size_to_UInt32 start) (size_to_UInt32 n)))
let sub #a #len #olen b start n =
  Buf.sub b (size_to_UInt32 start) (size_to_UInt32 n)

inline_for_extraction
val index:
  #a:Type0 -> #len:size_nat ->
  b:lbuffer a len -> i:size_t{v i < len} -> Stack a
  (requires (fun h0 -> Buf.live h0 b))
  (ensures (fun h0 r h1 -> h0 == h1 /\ r == Seq.index (Buf.as_seq h1 b) (v i)))
let index #a #len b i =
  Buf.index b (size_to_UInt32 i)

inline_for_extraction
val upd:
  #a:Type0 -> #len:size_nat{len > 0} ->
  b:lbuffer a len -> i:size_t{v i < len} ->
  x:a -> Stack unit
  (requires (fun h0 -> Buf.live h0 b))
  (ensures (fun h0 _ h1 ->
    Buf.modifies_1 b h0 h1 /\ Buf.live h1 b /\
    Buf.as_seq h1 b == Seq.upd (Buf.as_seq h0 b) (v i) x))
let upd #a #len b i v =
  Buf.upd b (size_to_UInt32 i) v

inline_for_extraction let op_Array_Assignment #a #len = upd #a #len
inline_for_extraction let op_Array_Access #a #len = index #a #len

inline_for_extraction
val create:
  #a:Type0 -> #len:size_nat{len > 0} ->
  clen:size_t{v clen == len} -> init:a -> StackInline (lbuffer a len)
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 ->
    Buf.alloc_post_common (HS.get_tip h0) len r h0 h1 /\
    Buf.as_seq h1 r == Seq.create len init))
let create #a #len clen init =
  Buf.alloca init (size_to_UInt32 clen)

inline_for_extraction
val createL:
  #a:Type0 -> init:list a{List.Tot.length init <= max_size_t} ->
  StackInline (lbuffer a (List.Tot.length init))
  (requires (fun h0 -> Buf.alloc_of_list_pre #a init))
  (ensures (fun h0 r h1 ->
    let len = FStar.List.Tot.length init in
    Buf.alloc_post_common (HS.get_tip h0) len r h0 h1 /\
    Buf.as_seq h1 r == Seq.of_list init /\
    Buf.alloc_of_list_post #a len r))
let createL #a init =
  Buf.alloca_of_list init

inline_for_extraction
val recall
  (#a:Type)
  (#len:size_nat)
  (b:lbuffer a len)
: Stack unit
  (requires (fun _ -> Buf.recallable b))
  (ensures  (fun m0 _ m1 -> m0 == m1 /\ Buf.live m1 b))
let recall #a #len b = Buf.recall b

inline_for_extraction
val createL_global:
  #a:Type0 -> init:list a{List.Tot.length init <= max_size_t} ->
  ST (lbuffer a (List.Tot.length init))
  (requires fun h0 -> Buf.alloc_of_list_pre #a init)
  (ensures  fun h0 b h1 ->
    let len = FStar.List.Tot.length init in
    Buf.recallable b /\
    Buf.alloc_post_static HyperStack.root len b /\
    Buf.alloc_of_list_post len b /\
    Buf.alloc_post_common HyperStack.root len b h0 h1 /\
    Buf.as_seq h1 b == Seq.of_list init)
let createL_global #a init =
  Buf.gcmalloc_of_list HyperStack.root init


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
//   (requires (fun h0 -> Buf.live h0 o /\ Buf.live h0 i /\ Buf.disjoint i o))
//   (ensures (fun h0 _ h1 ->
//     Buf.live h1 o /\ Buf.live h1 i /\ modifies (loc_buffer o) h0 h1 /\
//     Buf.as_seq h1 o == Buf.as_seq h0 i))
// let copy #a #len o clen i =
//   let h0 = ST.get() in
//   let inv (h1:mem) (j:nat{j <= len}) =
//     Buf.live h1 o /\ Buf.live h1 i /\
//     modifies (loc_buffer o) h0 h1 /\
//     Seq.slice (Buf.as_seq h1 o) 0 j == Seq.slice (Buf.as_seq h0 i) 0 j in
//   let f' (j:size_t{0 <= v j /\ v j < len}) : Stack unit
//       (requires (fun h -> inv h (v j)))
//       (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
//       let h1 = ST.get () in
//       let src_i = i.(j) in
//       o.(j) <- src_i;
//       let h2 = ST.get () in
//       lemma_seq_slice_index (Buf.as_seq h2 o) (Buf.as_seq h0 i) (v j);
//       modifies_trans (loc_buffer o) h0 h1 (loc_buffer o) h2 in
//   Lib.Loops.for (size 0) clen inv f'

inline_for_extraction
val copy:
  #a:Type -> #len:size_nat ->
  o:lbuffer a len -> clen:size_t{v clen == len} ->
  i:lbuffer a len -> Stack unit
  (requires (fun h0 -> Buf.live h0 o /\ Buf.live h0 i /\ Buf.disjoint i o))
  (ensures (fun h0 _ h1 ->
    Buf.live h1 o /\ Buf.live h1 i /\ modifies (loc_buffer o) h0 h1 /\
    Buf.as_seq h1 o == Buf.as_seq h0 i))
let copy #a #len o clen i =
  let h0 = ST.get () in
  LowStar.BufferOps.blit i (size_to_UInt32 (size 0)) o (size_to_UInt32 (size 0)) (size_to_UInt32 clen);
  let h1 = ST.get () in
  assert (Seq.slice (Buf.as_seq h1 o) 0 len == Seq.slice (Buf.as_seq h0 i) 0 len)

let loop_nospec_inv (#a:Type) (h0:mem) (h1:mem)
		    (len:size_nat) (n:size_nat)
		    (buf:lbuffer a len) (i:size_nat{i <= n}): Type =
   Buf.live h0 buf /\ Buf.live h1 buf /\ modifies (loc_buffer buf) h0 h1

inline_for_extraction
val loop_nospec:
  #h0:mem -> #a:Type0 -> #len:size_nat ->
  n:size_t -> buf:lbuffer a len ->
  impl:
    (i:size_t{v i < v n} -> Stack unit
      (requires fun h -> loop_nospec_inv #a h0 h len (v n) buf (v i))
      (ensures  fun _ r h1 -> loop_nospec_inv #a h0 h1 len (v n) buf (v i + 1))) -> Stack unit
  (requires (fun h -> h0 == h /\ Buf.live h0 buf))
  (ensures (fun _ _ h1 -> Buf.live h1 buf /\ modifies (loc_buffer buf) h0 h1))
let loop_nospec #h0 #a #len n buf impl =
  let inv (h1:mem) (j:nat{j <= v n}) =
    loop_nospec_inv #a h0 h1 len (v n) buf j in
  let f' (j:size_t{0 <= v j /\ v j < v n}): Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun _ _ h2 -> inv h2 (v j + 1))) =
      impl j in
  Lib.Loops.for (size 0) n inv f'

inline_for_extraction
val uint_from_bytes_le:
  #t:m_inttype{~(SIZE? t)} ->
  i:lbuffer uint8 (numbytes t) ->
  Stack (uint_t t)
  (requires (fun h0 -> Buf.live h0 i))
  (ensures (fun h0 o h1 -> h0 == h1 /\ Buf.live h1 i))
let uint_from_bytes_le #t i =
  match t with
  | U8 -> i.(size 0)
  | U16 -> let u = C.load16_le i in u16_from_UInt16 u
  | U32 -> let u = C.load32_le i in u32_from_UInt32 u
  | U64 -> let u = C.load64_le i in u64_from_UInt64 u
  | U128 -> let u = C.load128_le i in u128_from_UInt128 u

inline_for_extraction
val uint_from_bytes_be:
  #t:m_inttype{~(SIZE? t)} ->
  i:lbuffer uint8 (numbytes t) -> Stack (uint_t t)
  (requires (fun h0 -> Buf.live h0 i))
  (ensures (fun h0 o h1 -> h0 == h1 /\ Buf.live h1 i))
let uint_from_bytes_be #t i =
  match t with
  | U8 -> i.(size 0)
  | U16 -> let u = C.load16_be i in u16_from_UInt16 u
  | U32 -> let u = C.load32_be i in u32_from_UInt32 u
  | U64 -> let u = C.load64_be i in u64_from_UInt64 u
  | U128 -> let u = C.load128_be i in u128_from_UInt128 u

inline_for_extraction
val uint_to_bytes_le:
  #t:m_inttype{~(SIZE? t)} ->
  o:lbuffer uint8 (numbytes t) ->
  i:uint_t t -> Stack unit
  (requires (fun h0 -> Buf.live h0 o))
  (ensures (fun h0 _ h1 -> Buf.live h1 o /\ modifies (loc_buffer o) h0 h1))
let uint_to_bytes_le #t o i =
  match t with
  | U8 -> o.(size 0) <- i
  | U16 -> C.store16_le o (u16_to_UInt16 i)
  | U32 -> C.store32_le o (u32_to_UInt32 i)
  | U64 -> C.store64_le o (u64_to_UInt64 i)
  | U128 -> C.store128_le o (u128_to_UInt128 i)

inline_for_extraction
val uint_to_bytes_be:
  #t:m_inttype{~(SIZE? t)} ->
  o:lbuffer uint8 (numbytes t) ->
  i:uint_t t -> Stack unit
  (requires (fun h0 -> Buf.live h0 o))
  (ensures (fun h0 _ h1 -> Buf.live h1 o /\ modifies (loc_buffer o) h0 h1))
let uint_to_bytes_be #t o i =
  match t with
  | U8 -> o.(size 0) <- i
  | U16 -> C.store16_be o (u16_to_UInt16 i)
  | U32 -> C.store32_be o (u32_to_UInt32 i)
  | U64 -> C.store64_be o (u64_to_UInt64 i)
  | U128 -> C.store128_be o (u128_to_UInt128 i)

assume val print_compare_display:
  len:size_t -> lbuffer uint8 (size_v len) ->
  lbuffer uint8 (size_v len) -> Stack unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
