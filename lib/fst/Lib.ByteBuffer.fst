module Lib.ByteBuffer

open FStar.HyperStack
open FStar.HyperStack.ST

open LowStar.Buffer

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module ByteSeq = Lib.ByteSequence

friend Lib.IntTypes
friend Lib.ByteSequence
friend Lib.Buffer


#set-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 0"

let lbytes_eq #len a b =
  push_frame();
  let res = create #bool #1 (size 1) true in
  [@ inline_let]
  let refl h _ = B.get h res 0 in
  [@ inline_let]
  let spec h0 = ByteSeq.lbytes_eq_inner #(v len) (B.as_seq h0 a) (B.as_seq h0 b) in
  let h0 = ST.get () in
  loop h0 len (ByteSeq.lbytes_eq_state (v len)) refl
    (fun i -> B.loc_buffer res) spec
    (fun i ->
      //Seq.unfold_repeat (v len) (fun _ -> bool) (spec h0) true (v i);
      let ai = a.(i) in
      let bi = b.(i) in
      let res0 = res.(size 0) in
      res.(size 0) <- res0 && FStar.UInt8.(u8_to_UInt8 ai =^ u8_to_UInt8 bi)
    );
  let res = res.(size 0) in
  pop_frame();
  res

// TODO: Fix this
#set-options "--admit_smt_queries true"

let uint_from_bytes_le #t #l i =
  match t with
  | U8 -> index #_ #(numbytes U8) i (size 0)
  | U16 -> let u = C.load16_le i in u16_from_UInt16 u
  | U32 -> let u = C.load32_le i in u32_from_UInt32 u
  | U64 -> let u = C.load64_le i in u64_from_UInt64 u
  | U128 -> let u = C.load128_le i in u128_from_UInt128 u

let uint_from_bytes_be #t #l i =
  match t with
  | U8 -> index #_ #(numbytes U8) i (size 0)
  | U16 -> let u = C.load16_be i in u16_from_UInt16 u
  | U32 -> let u = C.load32_be i in u32_from_UInt32 u
  | U64 -> let u = C.load64_be i in u64_from_UInt64 u
  | U128 -> let u = C.load128_be i in u128_from_UInt128 u

let uint_to_bytes_le #t #l o i =
  match t with
  | U8 -> upd #_ #(numbytes U8) o (size 0) i
  | U16 -> C.store16_le o (u16_to_UInt16 i)
  | U32 -> C.store32_le o (u32_to_UInt32 i)
  | U64 -> C.store64_le o (u64_to_UInt64 i)
  | U128 -> C.store128_le o (u128_to_UInt128 i)

let uint_to_bytes_be #t #l o i =
  match t with
  | U8 -> upd #_ #(numbytes U8) o (size 0) i
  | U16 -> C.store16_be o (u16_to_UInt16 i)
  | U32 -> C.store32_be o (u32_to_UInt32 i)
  | U64 -> C.store64_be o (u64_to_UInt64 i)
  | U128 -> C.store128_be o (u128_to_UInt128 i)

inline_for_extraction
let uints_from_bytes_le #t #l #len o clen i =
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) =  True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let b_i = sub #uint8 #(len `op_Multiply` numbytes t) #len i (mul_mod j (size (numbytes t))) (size (numbytes t)) in
      let u_i = uint_from_bytes_le b_i in
      upd #_ #len o j u_i in
  Lib.Loops.for (size 0) clen inv f'

inline_for_extraction
let uints_from_bytes_be #t #l #len o clen i =
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) =  True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let b_i = sub #uint8 #(len `op_Multiply` numbytes t) #len i (mul_mod j (size (numbytes t))) (size (numbytes t)) in
      let u_i = uint_from_bytes_be b_i in
      upd #_ #len o j u_i in
  Lib.Loops.for (size 0) clen inv f'

inline_for_extraction
let uints_to_bytes_le #t #l #len o clen i =
  let h0 = ST.get () in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
    (requires (fun h -> inv h (v j)))
    (ensures  (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let u_i = index #_ #len i j in
      let b_i = sub #_ #(len `op_Multiply` (numbytes t)) #(numbytes t) o (mul_mod j (size (numbytes t))) (size (numbytes t)) in
      uint_to_bytes_le b_i u_i in
  Lib.Loops.for (size 0) clen inv f'

inline_for_extraction
let uints_to_bytes_be #t #l #len o clen i =
  let h0 = ST.get () in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
    (requires (fun h -> inv h (v j)))
    (ensures  (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let u_i = index #_ #len i j in
      let b_i = sub #_ #((len `op_Multiply` (numbytes t))) #(numbytes t) o (mul_mod j (size (numbytes t))) (size (numbytes t)) in
      uint_to_bytes_be b_i u_i in
  Lib.Loops.for (size 0) clen inv f'
