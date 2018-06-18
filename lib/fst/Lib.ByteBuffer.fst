module Lib.ByteBuffer

open FStar.HyperStack
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.ByteSequence

module LSeq = Lib.Sequence

module Buf = LowStar.Buffer
module U32 = FStar.UInt32


inline_for_extraction
let uint_from_bytes_le #t i =
  match t with
  | U8 -> i.(size 0)
  | U16 -> let u = C.load16_le i in u16_from_UInt16 u
  | U32 -> let u = C.load32_le i in u32_from_UInt32 u
  | U64 -> let u = C.load64_le i in u64_from_UInt64 u
  | U128 -> let u = C.load128_le i in u128_from_UInt128 u

inline_for_extraction
let uint_from_bytes_be #t i =
  match t with
  | U8 -> i.(size 0)
  | U16 -> let u = C.load16_be i in u16_from_UInt16 u
  | U32 -> let u = C.load32_be i in u32_from_UInt32 u
  | U64 -> let u = C.load64_be i in u64_from_UInt64 u
  | U128 -> let u = C.load128_be i in u128_from_UInt128 u

inline_for_extraction
let uint_to_bytes_le #t o i =
  match t with
  | U8 -> o.(size 0) <- i
  | U16 -> C.store16_le o (u16_to_UInt16 i)
  | U32 -> C.store32_le o (u32_to_UInt32 i)
  | U64 -> C.store64_le o (u64_to_UInt64 i)
  | U128 -> C.store128_le o (u128_to_UInt128 i)

inline_for_extraction
let uint_to_bytes_be #t o i =
  match t with
  | U8 -> o.(size 0) <- i
  | U16 -> C.store16_be o (u16_to_UInt16 i)
  | U32 -> C.store32_be o (u32_to_UInt32 i)
  | U64 -> C.store64_be o (u64_to_UInt64 i)
  | U128 -> C.store128_be o (u128_to_UInt128 i)


inline_for_extraction
let uints_from_bytes_le #t #len o clen i =
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) =  True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let b_i = sub #uint8 #(len `op_Multiply` numbytes t) #len i (mul_mod #SIZE j (size (numbytes t))) (size (numbytes t)) in
      let u_i = uint_from_bytes_le b_i in
      o.(j) <- u_i in
  Lib.Loops.for (size 0) clen inv f'


inline_for_extraction
let uints_from_bytes_be #t #len o clen i =
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) =  True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let b_i = sub #uint8 #(len `op_Multiply` numbytes t) #len i (mul_mod #SIZE j (size (numbytes t))) (size (numbytes t)) in
      let u_i = uint_from_bytes_be b_i in
      o.(j) <- u_i in
  Lib.Loops.for (size 0) clen inv f'



inline_for_extraction
let uints_to_bytes_le #t #len o clen i =
  let h0 = ST.get () in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
    (requires (fun h -> inv h (v j)))
    (ensures  (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let u_i = index i j in
      let b_i = sub o (mul_mod #SIZE j (size (numbytes t))) (size (numbytes t)) in
      uint_to_bytes_le b_i u_i in
  Lib.Loops.for (size 0) clen inv f'


inline_for_extraction
let uints_to_bytes_be #t #len o clen i =
  let h0 = ST.get () in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
    (requires (fun h -> inv h (v j)))
    (ensures  (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let u_i = index i j in
      let b_i = sub o (mul_mod #SIZE j (size (numbytes t))) (size (numbytes t)) in
      uint_to_bytes_be b_i u_i in
  Lib.Loops.for (size 0) clen inv f'

