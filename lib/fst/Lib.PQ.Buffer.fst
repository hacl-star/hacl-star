module Lib.PQ.Buffer

open FStar.HyperStack
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence

module Buf = LowStar.Buffer
module U32 = FStar.UInt32

unfold let v = size_v

type lbuffer (a:Type0) (len:size_nat) = b:Buf.buffer a {Buf.length b == len}

inline_for_extraction
val sub:
  #a:Type0 -> #len:size_nat -> #olen:size_nat ->
  b:lbuffer a len -> start:size_t ->
  n:size_t{v start + v n <= len /\ v n == olen} -> Stack (lbuffer a olen)
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> True))
let sub #a #len #olen b start n =
  admit();
  Buf.sub b (size_to_UInt32 start) (size_to_UInt32 n)

inline_for_extraction
val slice:
  #a:Type0 -> #len:size_nat -> #olen:size_nat ->
  b:lbuffer a len -> start:size_t ->
  fin:size_t{v start <= v fin /\ v fin <= len /\ v fin - v start == olen} -> Stack (lbuffer a olen)
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> True))
let slice #a #len #olen b start n =
  admit();
  Buf.sub b (size_to_UInt32 start) (size_to_UInt32 (n -. start))

inline_for_extraction
val index:
  #a:Type0 -> #len:size_nat ->
  b:lbuffer a (len) -> i:size_t{v i < len} -> Stack a
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> True))
let index #a #len b i =
  admit();
  Buf.index b (size_to_UInt32 i)

inline_for_extraction
val upd:
  #a:Type0 -> #len:size_nat ->
  b:lbuffer a (len) -> i:size_t{v i < len} ->
  x:a -> Stack unit
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> True))
let upd #a #len b i v =
  admit();
  Buf.upd b (size_to_UInt32 i) v

inline_for_extraction let op_Array_Assignment #a #len = upd #a #len
inline_for_extraction let op_Array_Access #a #len = index #a #len

inline_for_extraction
val create:
  #a:Type0 -> #len:size_nat ->
  clen:size_t{v clen == len} -> init:a -> StackInline (lbuffer a len)
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> True))
let create #a #len clen init =
  admit();
  Buf.alloca init (size_to_UInt32 clen)

inline_for_extraction
val createL:
  #a:Type0 -> init:list a{List.Tot.length init <= max_size_t} ->
  StackInline (lbuffer a (List.Tot.length init))
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> True))
let createL #a init =
  admit();
  Buf.alloca_of_list init

inline_for_extraction
val createL_global:
  #a:Type0 -> init:list a{List.Tot.length init <= max_size_t} ->
  ST (lbuffer a (List.Tot.length init))
  (requires fun h0 -> True)
  (ensures  fun h0 r h1 -> True)
let createL_global #a init =
  admit();
  Buf.gcmalloc_of_list HyperStack.root init

inline_for_extraction
val copy:
  #a:Type -> #len:size_nat ->
  o:lbuffer a len -> clen:size_t{v clen == len} ->
  i:lbuffer a len -> Stack unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> True))
let copy #a #len o clen i =
  admit();
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let src_i = i.(j) in
      o.(j) <- src_i in
  Lib.Loops.for (size 0) clen inv f'

inline_for_extraction
val loop_nospec:
  #h0:mem -> #a:Type0 -> #len:size_nat ->
  n:size_t -> buf:lbuffer a len ->
  impl:(i:size_t{v i < v n} ->
	Stack unit (requires fun h0 -> True) (ensures  fun h0 r h1 -> True)) -> Stack unit
  (requires (fun h -> True))
  (ensures (fun _ _ h1 -> True))
let loop_nospec #h0 #a #len n buf impl =
  admit();
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      impl j in
  Lib.Loops.for (size 0) n inv f'



inline_for_extraction
val uint_from_bytes_le:
  #t:m_inttype ->
  i:lbuffer uint8 (numbytes t) ->
  Stack (uint_t t)
  (requires (fun h0 -> True))
  (ensures (fun h0 o h1 -> True))
let uint_from_bytes_le #t i =
  admit();
  match t with
  | U8 -> i.(size 0)
  | U16 -> let u = C.load16_le i in u16_from_UInt16 u
  | U32 -> let u = C.load32_le i in u32_from_UInt32 u
  | U64 -> let u = C.load64_le i in u64_from_UInt64 u
  | U128 -> let u = C.load128_le i in u128_from_UInt128 u

inline_for_extraction
val uint_from_bytes_be:
  #t:m_inttype ->
  i:lbuffer uint8 (numbytes t) -> Stack (uint_t t)
  (requires (fun h0 -> True))
  (ensures (fun h0 o h1 -> True))
let uint_from_bytes_be #t i =
  admit();
  match t with
  | U8 -> i.(size 0)
  | U16 -> let u = C.load16_be i in u16_from_UInt16 u
  | U32 -> let u = C.load32_be i in u32_from_UInt32 u
  | U64 -> let u = C.load64_be i in u64_from_UInt64 u
  | U128 -> let u = C.load128_be i in u128_from_UInt128 u

inline_for_extraction
val uint_to_bytes_le:
  #t:m_inttype ->
  o:lbuffer uint8 (numbytes t) ->
  i:uint_t t -> Stack unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> True))
let uint_to_bytes_le #t o i =
  admit();
  match t with
  | U8 -> o.(size 0) <- i
  | U16 -> C.store16_le o (u16_to_UInt16 i)
  | U32 -> C.store32_le o (u32_to_UInt32 i)
  | U64 -> C.store64_le o (u64_to_UInt64 i)
  | U128 -> C.store128_le o (u128_to_UInt128 i)

inline_for_extraction
val uint_to_bytes_be:
  #t:m_inttype ->
  o:lbuffer uint8 (numbytes t) ->
  i:uint_t t -> Stack unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> True))
let uint_to_bytes_be #t o i =
  admit();
  match t with
  | U8 -> o.(size 0) <- i
  | U16 -> C.store16_be o (u16_to_UInt16 i)
  | U32 -> C.store32_be o (u32_to_UInt32 i)
  | U64 -> C.store64_be o (u64_to_UInt64 i)
  | U128 -> C.store128_be o (u128_to_UInt128 i)

assume val print_compare_display: 
  len:size_t -> lbuffer uint8 (size_v len) -> 
  lbuffer uint8 (size_v len) -> Stack unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
