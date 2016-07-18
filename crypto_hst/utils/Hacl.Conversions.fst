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

let u32 = FStar.UInt32.t
let u64 = FStar.UInt64.t
let s64 = Hacl.UInt64.t
let s32 = Hacl.UInt32.t
let s8 = Hacl.UInt8.t
let uint32s = Hacl.SBuffer.u32s
let bytes = Hacl.SBuffer.u8s


#set-options "--lax"


let op_At_Amp (a:s64) (s:s64) : Tot s64 = Hacl.UInt64.logand a s

val be_bytes_of_sint64: x:bytes -> y:s64
  -> STL unit (requires (fun h -> live h x)) (ensures (fun h0 _ h1 -> live h1 x /\ modifies_1 x h0 h1))
let be_bytes_of_sint64 output x =
 let b0 = sint64_to_sint8 ((Hacl.UInt64.shift_right x 56ul) @& uint64_to_sint64 255UL) in
 let b1 = sint64_to_sint8 ((Hacl.UInt64.shift_right x 48ul) @& uint64_to_sint64 255UL) in
 let b2 = sint64_to_sint8 ((Hacl.UInt64.shift_right x 40ul) @& uint64_to_sint64 255UL) in
 let b3 = sint64_to_sint8 ((Hacl.UInt64.shift_right x 32ul) @& uint64_to_sint64 255UL) in
 let b4 = sint64_to_sint8 ((Hacl.UInt64.shift_right x 24ul) @& uint64_to_sint64 255UL) in
 let b5 = sint64_to_sint8 ((Hacl.UInt64.shift_right x 16ul) @& uint64_to_sint64 255UL) in
 let b6 = sint64_to_sint8 ((Hacl.UInt64.shift_right x 8ul)  @& uint64_to_sint64 255UL) in
 let b7 = sint64_to_sint8 ((x)                              @& uint64_to_sint64 255UL) in
 upd output 0ul b0;
 upd output (1ul) b1;
 upd output (2ul) b2;
 upd output (3ul) b3;
 upd output (4ul) b4;
 upd output (5ul) b5;
 upd output (6ul) b6;
 upd output (7ul) b7

let op_At_At_Amp = UInt64.logand

val be_bytes_of_uint64: x:bytes -> y:u64
  -> STL unit
        (requires (fun h -> live h x))
        (ensures  (fun h0 _ h1 -> live h1 x /\ modifies_1 x h0 h1))

let be_bytes_of_uint64 output x =
 let b0 = uint64_to_sint8 ((UInt64.shift_right x 56ul) @@& 255UL) in
 let b1 = uint64_to_sint8 ((UInt64.shift_right x 48ul) @@& 255UL) in
 let b2 = uint64_to_sint8 ((UInt64.shift_right x 40ul) @@& 255UL) in
 let b3 = uint64_to_sint8 ((UInt64.shift_right x 32ul) @@& 255UL) in
 let b4 = uint64_to_sint8 ((UInt64.shift_right x 24ul) @@& 255UL) in
 let b5 = uint64_to_sint8 ((UInt64.shift_right x 16ul) @@& 255UL) in
 let b6 = uint64_to_sint8 ((UInt64.shift_right x 8ul)  @@& 255UL) in
 let b7 = uint64_to_sint8 ((x)                         @@& 255UL) in
 upd output 0ul b0;
 upd output (1ul) b1;
 upd output (2ul) b2;
 upd output (3ul) b3;
 upd output (4ul) b4;
 upd output (5ul) b5;
 upd output (6ul) b6;
 upd output (7ul) b7

val be_uint32_of_bytes: b:bytes{length b >= 4} -> STL s32
  (requires (fun h -> live h b))
  (ensures (fun h0 r h1 -> h0 == h1 /\ live h0 b))
let be_uint32_of_bytes (b:bytes{length b >= 4}) =
  let b0 = (index b 0ul) in
  let b1 = (index b 1ul) in
  let b2 = (index b 2ul) in
  let b3 = (index b 3ul) in
  let r = (sint8_to_sint32 b3)
	+%^ (op_Less_Less_Hat (sint8_to_sint32 b2) 8ul)
	+%^ (op_Less_Less_Hat (sint8_to_sint32 b1) 16ul)
	+%^ (op_Less_Less_Hat (sint8_to_sint32 b0) 24ul) in
  r

val be_uint32s_of_bytes:uint32s -> bytes -> u32 -> St unit
let rec be_uint32s_of_bytes u b len =
  if UInt32.eq len 0ul then ()
  else (
    let l4 = UInt32.div len 4ul in
    upd u (UInt32.sub l4 1ul) (be_uint32_of_bytes (sub b (UInt32.sub len 4ul) 4ul));
    be_uint32s_of_bytes u b (UInt32.sub len 4ul)
  )

let op_Hat_Greater_Greater (a:s32) (b:u32) : Tot s32 = Hacl.UInt32.shift_right a b

val be_bytes_of_uint32s: output:bytes -> m:uint32s{disjoint output m} -> len:u32{v len <=length output /\ v len<=op_Multiply 4 (length m)} -> STL unit
  (requires (fun h -> live h output /\ live h m))
  (ensures (fun h0 _ h1 -> live h0 output /\ live h0 m /\ live h1 output /\ live h1 m
    /\ modifies_1 output h0 h1 ))
let rec be_bytes_of_uint32s output m len =
  if len =^ 0ul then ()
  else
    begin
      let l4 = UInt32.div len 4ul in
      let l = UInt32.sub l4 1ul in
      let x = index m l in
      let b0 = sint32_to_sint8 ((x ^>> 24ul) &^ uint32_to_sint32 255ul) in
      let b1 = sint32_to_sint8 ((x ^>> 16ul) &^ uint32_to_sint32 255ul) in
      let b2 = sint32_to_sint8 ((x ^>> 8ul)  &^ uint32_to_sint32 255ul) in
      let b3 = sint32_to_sint8 ((x)          &^ uint32_to_sint32 255ul) in
      let l4 = UInt32.sub len 4ul in
      upd output l4 b0;
      upd output (UInt32.add l4 1ul) b1;
      upd output (UInt32.add l4 2ul) b2;
      upd output (UInt32.add l4 3ul) b3;
      be_bytes_of_uint32s output m l4
    end
