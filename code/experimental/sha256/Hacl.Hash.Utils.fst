module Hacl.Hash.Utils

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.ST
open FStar.Buffer

open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module S8 = Hacl.UInt8
module S32 = Hacl.UInt32
module S64 = Hacl.UInt64

module Buffer = FStar.Buffer
module Cast = Hacl.Cast


(* Definition of base types *)
let uint8_t   = FStar.UInt8.t
let uint32_t  = FStar.UInt32.t
let uint64_t  = FStar.UInt64.t

let suint8_t  = Hacl.UInt8.t
let suint32_t = Hacl.UInt32.t
let suint64_t = Hacl.UInt64.t

let suint32_p = Buffer.buffer suint32_t
let suint8_p  = Buffer.buffer suint8_t


(* Definitions of aliases for functions *)
let u8_to_s8 = Cast.uint8_to_sint8
let u32_to_s32 = Cast.uint32_to_sint32
let u32_to_s64 = Cast.uint32_to_sint64
let s32_to_s8  = Cast.sint32_to_sint8
let s32_to_s64 = Cast.sint32_to_sint64
let u64_to_s64 = Cast.uint64_to_sint64



val upd4: buf:suint32_p{length buf <= pow2 32} -> idx:uint32_t{U32.v idx + 3 < length buf /\ U32.v idx + 3 <= pow2 32} -> a:uint32_t -> b:uint32_t -> c:uint32_t -> d:uint32_t
  -> Stack unit (requires (fun h -> live h buf))
               (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1))

let upd4 buf idx a b c d =
  buf.(idx +^ 0ul) <- u32_to_s32 a;
  buf.(idx +^ 1ul) <- u32_to_s32 b;
  buf.(idx +^ 2ul) <- u32_to_s32 c;
  buf.(idx +^ 3ul) <- u32_to_s32 d



(* Definition of the right rotation function for UInt32.t *)
let rotate_right (a:suint32_t) (b:uint32_t{v b <= 32}) : Tot suint32_t =
  S32.logor (S32.shift_right a b) (S32.shift_left a (U32.sub 32ul b))


val be_bytes_of_sint32: b:suint8_p{length b >= 4} -> x:suint32_t
  -> Stack unit
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


val be_sint32_of_bytes: b:suint8_p{length b >= 4}
  -> Stack suint32_t
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

val be_bytes_of_sint64: b:suint8_p{length b >= 8} -> x:suint64_t
  -> Stack unit
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


#set-options "--lax"

val be_bytes_of_uint32s: 
  output:suint8_p -> 
  m:suint32_p -> 
  len:uint32_t{U32.v len <= length output /\ U32.v len <= Prims.op_Multiply 4 (length m)} 
  -> Stack unit
          (requires (fun h -> live h output /\ live h m))
          (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 ))

let rec be_bytes_of_uint32s output m len =
  if len =^ 0ul then ()
  else
    begin
      let l4 = U32.div len 4ul in
      let l = U32.sub l4 1ul in
      let x = Buffer.index m l in
      let b0 = s32_to_s8 S32.((x >>^ 24ul) &^ u32_to_s32 255ul) in
      let b1 = s32_to_s8 S32.((x >>^ 16ul) &^ u32_to_s32 255ul) in
      let b2 = s32_to_s8 S32.((x >>^ 8ul)  &^ u32_to_s32 255ul) in
      let b3 = s32_to_s8 S32.((x)          &^ u32_to_s32 255ul) in
      let l4 = U32.sub len 4ul in
      Buffer.upd output l4 b0;
      Buffer.upd output (U32.add l4 1ul) b1;
      Buffer.upd output (U32.add l4 2ul) b2;
      Buffer.upd output (U32.add l4 3ul) b3;
      be_bytes_of_uint32s output m l4
    end


val be_uint32s_of_bytes:
  a:suint32_p ->
  b:suint8_p ->
  len:uint32_t ->
  Stack unit
        (requires (fun h -> live h a /\ live h b))
        (ensures  (fun h0 _ h1 -> live h1 a /\ live h1 b /\ modifies_1 a h0 h1))
let rec be_uint32s_of_bytes u b len =
  if U32.eq len 0ul then ()
  else (
    let l4 = U32.div len 4ul in
    upd u (U32.sub l4 1ul) (be_sint32_of_bytes (Buffer.sub b (U32.sub len 4ul) 4ul));
    be_uint32s_of_bytes u b (U32.sub len 4ul))
