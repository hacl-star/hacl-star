module Hacl.Conversions

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.Buffer
open FStar.UInt32
open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open Hacl.SBuffer
open Hacl.Operations


module U8 = FStar.UInt8
module S8 = Hacl.UInt8
module U32 = FStar.UInt32
module S32 = Hacl.UInt32
module U64 = FStar.UInt64
module S64 = Hacl.UInt64
module SB  = Hacl.SBuffer

let u8 = FStar.UInt8.t
let s8 = Hacl.UInt8.t
let u32 = FStar.UInt32.t
let s32 = Hacl.UInt32.t
let u64 = FStar.UInt64.t
let s64 = Hacl.UInt64.t
let uint32s = Hacl.SBuffer.u32s
let bytes = Hacl.SBuffer.u8s



//
// All this **** is required because the way those things
// are formalized in Hacl is wrong. It should disappear when
// we change the representation of buffers in the F* stdlib.
//

val be_bytes_of_sint64: b:bytes{length b >= 8} -> x:s64
  -> STL unit
        (requires (fun h -> live h b))
        (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))

let be_bytes_of_sint64 output x =
 let b0 = sint64_to_sint8 (S64.logand (S64.shift_right x 56ul) (uint32_to_sint64 255ul)) in
 let b1 = sint64_to_sint8 (S64.logand (S64.shift_right x 48ul) (uint32_to_sint64 255ul)) in
 let b2 = sint64_to_sint8 (S64.logand (S64.shift_right x 40ul) (uint32_to_sint64 255ul)) in
 let b3 = sint64_to_sint8 (S64.logand (S64.shift_right x 32ul) (uint32_to_sint64 255ul)) in
 let b4 = sint64_to_sint8 (S64.logand (S64.shift_right x 24ul) (uint32_to_sint64 255ul)) in
 let b5 = sint64_to_sint8 (S64.logand (S64.shift_right x 16ul) (uint32_to_sint64 255ul)) in
 let b6 = sint64_to_sint8 (S64.logand (S64.shift_right x 8ul)  (uint32_to_sint64 255ul)) in
 let b7 = sint64_to_sint8 (S64.logand x (uint32_to_sint64 255ul)) in
 upd output 0ul b0;
 upd output 1ul b1;
 upd output 2ul b2;
 upd output 3ul b3;
 upd output 4ul b4;
 upd output 5ul b5;
 upd output 6ul b6;
 upd output 7ul b7


val be_bytes_of_uint64: b:bytes{length b >= 8} -> x:u64
  -> STL unit
        (requires (fun h -> live h b))
        (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))

let be_bytes_of_uint64 output x =
 let b0 = sint64_to_sint8 (S64.logand (uint64_to_sint64 (U64.shift_right x 56ul)) (uint32_to_sint64 255ul)) in
 let b1 = sint64_to_sint8 (S64.logand (uint64_to_sint64 (U64.shift_right x 48ul)) (uint32_to_sint64 255ul)) in
 let b2 = sint64_to_sint8 (S64.logand (uint64_to_sint64 (U64.shift_right x 40ul)) (uint32_to_sint64 255ul)) in
 let b3 = sint64_to_sint8 (S64.logand (uint64_to_sint64 (U64.shift_right x 32ul)) (uint32_to_sint64 255ul)) in
 let b4 = sint64_to_sint8 (S64.logand (uint64_to_sint64 (U64.shift_right x 24ul)) (uint32_to_sint64 255ul)) in
 let b5 = sint64_to_sint8 (S64.logand (uint64_to_sint64 (U64.shift_right x 16ul)) (uint32_to_sint64 255ul)) in
 let b6 = sint64_to_sint8 (S64.logand (uint64_to_sint64 (U64.shift_right x 8ul))  (uint32_to_sint64 255ul)) in
 let b7 = sint64_to_sint8 (S64.logand (uint64_to_sint64 x) (uint32_to_sint64 255ul)) in
 upd output 0ul b0;
 upd output 1ul b1;
 upd output 2ul b2;
 upd output 3ul b3;
 upd output 4ul b4;
 upd output 5ul b5;
 upd output 6ul b6;
 upd output 7ul b7


val be_bytes_of_sint32: b:bytes{length b >= 4} -> x:s32
  -> STL unit
        (requires (fun h -> live h b))
        (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))

let be_bytes_of_sint32 output x =
 let b0 = sint32_to_sint8 (S32.logand (S32.shift_right x 24ul) (uint32_to_sint32 255ul)) in
 let b1 = sint32_to_sint8 (S32.logand (S32.shift_right x 16ul) (uint32_to_sint32 255ul)) in
 let b2 = sint32_to_sint8 (S32.logand (S32.shift_right x 8ul)  (uint32_to_sint32 255ul)) in
 let b3 = sint32_to_sint8 (S32.logand x (uint32_to_sint32 255ul)) in
 upd output 0ul b0;
 upd output 1ul b1;
 upd output 2ul b2;
 upd output 3ul b3


val be_bytes_of_uint32: b:bytes{length b >= 4} -> y:u32
  -> STL unit
        (requires (fun h -> live h b))
        (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))

let be_bytes_of_uint32 output x =
 let b0 = uint32_to_sint8 (U32.logand (U32.shift_right x 24ul) 255ul) in
 let b1 = uint32_to_sint8 (U32.logand (U32.shift_right x 16ul) 255ul) in
 let b2 = uint32_to_sint8 (U32.logand (U32.shift_right x 8ul)  255ul) in
 let b3 = uint32_to_sint8 (U32.logand x 255ul) in
 upd output 0ul b0;
 upd output 1ul b1;
 upd output 2ul b2;
 upd output 3ul b3


val be_sint32_of_bytes: b:bytes{length b >= 4}
  -> STL s32
        (requires (fun h -> live h b))
        (ensures (fun h0 r h1 -> live h1 b /\ modifies_1 b h0 h1))

let be_sint32_of_bytes b =
  let b0 = index b 0ul in
  let b1 = index b 1ul in
  let b2 = index b 2ul in
  let b3 = index b 3ul in
  let r =
    S32.add_mod (S32.add_mod (S32.add_mod (sint8_to_sint32 b3)
                                          (S32.op_Less_Less_Hat (sint8_to_sint32 b2) 8ul))
	                          (S32.op_Less_Less_Hat (sint8_to_sint32 b1) 16ul))
                (S32.op_Less_Less_Hat (sint8_to_sint32 b0) 24ul) in
  r


#set-options "--lax"


val be_uint32s_of_bytes:uint32s -> b:bytes -> len:u32 -> St unit
let rec be_uint32s_of_bytes u b len =
  if U32.eq len 0ul then ()
  else (
    let l4 = U32.div len 4ul in
    upd u (U32.sub l4 1ul) (be_sint32_of_bytes (sub b (U32.sub len 4ul) 4ul));
    be_uint32s_of_bytes u b (U32.sub len 4ul)
  )

let op_Hat_Greater_Greater (a:s32) (b:u32) : Tot s32 = S32.shift_right a b

val be_bytes_of_uint32s: output:bytes -> m:uint32s{disjoint output m} -> len:u32{U32.v len <= length output /\ U32.v len <= Prims.op_Multiply 4 (SB.length m)} -> STL unit
  (requires (fun h -> live h output /\ live h m))
  (ensures (fun h0 _ h1 -> live h0 output /\ live h0 m /\ live h1 output /\ live h1 m
    /\ modifies_1 output h0 h1 ))
let rec be_bytes_of_uint32s output m len =
  if len =^ 0ul then ()
  else
    begin
      let l4 = U32.div len 4ul in
      let l = U32.sub l4 1ul in
      let x = index m l in
      let b0 = sint32_to_sint8 ((x ^>> 24ul) &^ uint32_to_sint32 255ul) in
      let b1 = sint32_to_sint8 ((x ^>> 16ul) &^ uint32_to_sint32 255ul) in
      let b2 = sint32_to_sint8 ((x ^>> 8ul)  &^ uint32_to_sint32 255ul) in
      let b3 = sint32_to_sint8 ((x)          &^ uint32_to_sint32 255ul) in
      let l4 = U32.sub len 4ul in
      SB.upd output l4 b0;
      SB.upd output (U32.add l4 1ul) b1;
      SB.upd output (U32.add l4 2ul) b2;
      SB.upd output (U32.add l4 3ul) b3;
      be_bytes_of_uint32s output m l4
    end
