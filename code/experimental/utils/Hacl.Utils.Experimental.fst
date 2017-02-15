module Hacl.Utils.Experimental

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


[@"c_inline"]
val upd4: buf:suint32_p{length buf <= pow2 32} -> idx:uint32_t{U32.v idx + 3 < length buf /\ U32.v idx + 3 <= pow2 32} -> a:uint32_t -> b:uint32_t -> c:uint32_t -> d:uint32_t
  -> Stack unit (requires (fun h -> live h buf))
               (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1))

[@"c_inline"]
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


val xor_bytes:
  output :suint8_p ->
  input  :suint8_p ->
  len    :uint32_t{U32.v len <= length output /\ U32.v len <= length input} ->
  Stack unit
        (requires (fun h0 -> live h0 output /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
        
let rec xor_bytes output input len =
  if U32.(len =^ 0ul) then ()
  else
    begin
      let i    = U32.(len -^ 1ul) in
      let in1i = Buffer.index input i in
      let oi   = Buffer.index output i in
      let oi   = S8.(in1i ^^ oi) in
      output.(i) <- oi;
      xor_bytes output input i
    end
    


val load32s_be:
  buf_32 :Buffer.buffer UInt32.t ->
  len_32 :UInt32.t{UInt32.v len_32 <= length buf_32} ->
  buf_8  :Buffer.buffer UInt8.t{ (UInt32.v len_32 * 4) <= length buf_8} ->
  Stack unit
        (requires (fun h0 -> live h0 buf_32 /\ live h0 buf_8))
        (ensures  (fun h0 _ h1 -> live h1 buf_32 /\ modifies_1 buf_32 h0 h1))

let rec load32s_be buf_32 len_32 buf_8 =
  if FStar.UInt32.(len_32 =^ 0ul) then ()
  else
    begin
      let x_8 = Buffer.sub buf_8 FStar.UInt32.((len_32 -^ 1ul) *^ 4ul) 4ul in
      let x_32 = Hacl.Endianness.load32_be x_8 in
      Buffer.upd buf_32 FStar.UInt32.(len_32 -^ 1ul) x_32;
      load32s_be buf_32 FStar.UInt32.(len_32 -^ 1ul) buf_8
    end


val store32s_be:
  buf_8  :buffer UInt8.t ->
  len_8 :UInt32.t{UInt32.v len_8 % 4 = 0 /\ UInt32.v len_8 <= length buf_8} ->
  buf_32 :buffer UInt32.t{UInt32.v len_8 <= (4 * length buf_32)} ->
  Stack unit
        (requires (fun h0 -> live h0 buf_8 /\ live h0 buf_32))
        (ensures  (fun h0 _ h1 -> live h1 buf_8 /\ modifies_1 buf_8 h0 h1))

let rec store32s_be buf_8 len_8 buf_32 =
  if FStar.UInt32.(len_8 =^ 0ul) then ()
  else
    begin
      cut((UInt32.v len_8 - 4)% 4 = 0);
      cut((UInt32.v len_8 - 4) <= length buf_8);
      let i_32 = FStar.UInt32.(len_8 /^ 4ul) in
      let x_32 = Buffer.index buf_32 FStar.UInt32.(i_32 -^ 1ul) in
      let x_8 = Buffer.sub buf_8 FStar.UInt32.((i_32 -^ 1ul) *^ 4ul) 4ul in
      Hacl.Endianness.store32_be x_8 x_32;
      store32s_be buf_8 FStar.UInt32.(len_8 -^ 4ul) buf_32
    end
