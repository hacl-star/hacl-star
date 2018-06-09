module Spec.Lib.IntBuf.LoadStore

open FStar.HyperStack
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntBuf

module LSeq = Spec.Lib.IntSeq

module Buf = FStar.Buffer
module U32 = FStar.UInt32


inline_for_extraction
let uints_from_bytes_le #t #len o i =
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) =  True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let b_i = sub #uint8 #(len `op_Multiply` numbytes t) #len i (mul_mod #SIZE j (size (numbytes t))) (size (numbytes t)) in
      let u_i = uint_from_bytes_le b_i in
      o.(j) <- u_i in
  Spec.Lib.Loops.for (size 0) (size len) inv f'


inline_for_extraction
let uints_from_bytes_be #t #len o i =
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) =  True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let b_i = sub #uint8 #(len `op_Multiply` numbytes t) #len i (mul_mod #SIZE j (size (numbytes t))) (size (numbytes t)) in
      let u_i = uint_from_bytes_be b_i in
      o.(j) <- u_i in
  Spec.Lib.Loops.for (size 0) (size len) inv f'



inline_for_extraction
let uints_to_bytes_le #t #len o i =
  let h0 = ST.get () in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
    (requires (fun h -> inv h (v j)))
    (ensures  (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let u_i = index i j in
      let b_i = sub o (mul_mod #SIZE j (size (numbytes t))) (size (numbytes t)) in
      uint_to_bytes_le b_i u_i in
  Spec.Lib.Loops.for (size 0) (size len) inv f'


inline_for_extraction
let uints_to_bytes_be #t #len o i =
  let h0 = ST.get () in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
    (requires (fun h -> inv h (v j)))
    (ensures  (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let u_i = index i j in
      let b_i = sub o (mul_mod #SIZE j (size (numbytes t))) (size (numbytes t)) in
      uint_to_bytes_be b_i u_i in
  Spec.Lib.Loops.for (size 0) (size len) inv f'

