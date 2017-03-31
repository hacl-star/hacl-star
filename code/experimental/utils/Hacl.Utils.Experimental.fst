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

module H8 = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64

module Cast = Hacl.Cast


(* Definition of base types *)
let uint8_t   = FStar.UInt8.t
let uint32_t  = FStar.UInt32.t
let uint64_t  = FStar.UInt64.t

let huint8_t  = Hacl.UInt8.t
let huint32_t = Hacl.UInt32.t
let huint64_t = Hacl.UInt64.t

let huint32_p = Buffer.buffer huint32_t
let huint8_p  = Buffer.buffer huint8_t


(* Definitions of aliases for functions *)
inline_for_extraction let u8_to_s8 = Cast.uint8_to_sint8
inline_for_extraction let u32_to_s32 = Cast.uint32_to_sint32
inline_for_extraction let u32_to_s64 = Cast.uint32_to_sint64
inline_for_extraction let s32_to_s8  = Cast.sint32_to_sint8
inline_for_extraction let s32_to_s64 = Cast.sint32_to_sint64
inline_for_extraction let u64_to_s64 = Cast.uint64_to_sint64


[@"substitute"]
val pupd_4: buf:huint32_p{length buf = 4} ->
  v0:uint32_t -> v1:uint32_t -> v2:uint32_t -> v3:uint32_t ->
  Stack unit (requires (fun h -> live h buf))
               (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                         /\ (let s = Hacl.Spec.Endianness.reveal_h32s (as_seq h1 buf) in
                           Seq.index s 0 == v0
                         /\ Seq.index s 1 == v1
                         /\ Seq.index s 2 == v2
                         /\ Seq.index s 3 == v3)))

[@"substitute"]
let pupd_4 buf v0 v1 v2 v3 =
  buf.(0ul) <- u32_to_s32 v0;
  buf.(1ul) <- u32_to_s32 v1;
  buf.(2ul) <- u32_to_s32 v2;
  buf.(3ul) <- u32_to_s32 v3


[@"substitute"]
val upd_4: buf:huint32_p{length buf <= pow2 32} -> idx:uint32_t{U32.v idx + 3 < length buf /\ U32.v idx + 3 <= pow2 32} -> v0:uint32_t -> v1:uint32_t -> v2:uint32_t -> v3:uint32_t
  -> Stack unit (requires (fun h -> live h buf))
               (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                         (* /\ (let s = as_seq h1 buf in *)
                         (* Seq.index s (U32.v idx + 0) == v0 /\ Seq.index s (U32.v idx + 1) == v1 /\ Seq.index s (U32.v idx + 2) == v2 /\ Seq.index s (U32.v idx + 3) == v3 )*)))
[@"substitute"]
let upd_4 buf idx v0 v1 v2 v3 =
  buf.(idx +^ 0ul) <- u32_to_s32 v0;
  buf.(idx +^ 1ul) <- u32_to_s32 v1;
  buf.(idx +^ 2ul) <- u32_to_s32 v2;
  buf.(idx +^ 3ul) <- u32_to_s32 v3


[@"substitute"]
val hupd_4: buf:huint32_p{length buf = 4} ->
  v0:H32.t -> v1:H32.t -> v2:H32.t -> v3:H32.t ->
  Stack unit (requires (fun h -> live h buf))
             (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                         /\ (let s = as_seq h1 buf in
                         Seq.index s 0 == v0 /\ Seq.index s 1 == v1 /\ Seq.index s 2 == v2 /\ Seq.index s 3 == v3)))

[@"substitute"]
let hupd_4 buf v0 v1 v2 v3 =
  buf.(0ul) <- v0;
  buf.(1ul) <- v1;
  buf.(2ul) <- v2;
  buf.(3ul) <- v3


[@"substitute"]
val aux_hupd_8: buf:huint32_p{length buf = 8} ->
  v0:H32.t -> v1:H32.t -> v2:H32.t -> v3:H32.t -> v4:H32.t -> v5:H32.t -> v6:H32.t -> v7:H32.t ->
  Stack unit (requires (fun h -> live h buf))
             (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                         /\ (let s = as_seq h1 buf in
                         Seq.index s 0 == v0 /\ Seq.index s 1 == v1 /\ Seq.index s 2 == v2 /\ Seq.index s 3 == v3 /\
                         Seq.index s 4 == v4 /\ Seq.index s 5 == v5 /\ Seq.index s 6 == v6 /\ Seq.index s 7 == v7)))

[@"substitute"]
let aux_hupd_8 buf v0 v1 v2 v3 v4 v5 v6 v7 =
  let p1 = Buffer.sub buf 0ul 4ul in
  let p2 = Buffer.sub buf 4ul 4ul in
  hupd_4 p1 v0 v1 v2 v3;
  hupd_4 p2 v4 v5 v6 v7


[@"substitute"]
val hupd_8: buf:huint32_p{length buf = 8} ->
  v0:H32.t -> v1:H32.t -> v2:H32.t -> v3:H32.t -> v4:H32.t -> v5:H32.t -> v6:H32.t -> v7:H32.t ->
  Stack unit (requires (fun h -> live h buf))
             (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                         /\ (let s = as_seq h1 buf in Seq.Create.create_8 v0 v1 v2 v3 v4 v5 v6 v7 == s)))

[@"substitute"]
let hupd_8 buf v0 v1 v2 v3 v4 v5 v6 v7 =
  aux_hupd_8 buf v0 v1 v2 v3 v4 v5 v6 v7;
  let h1 = ST.get () in
  Seq.lemma_eq_intro (as_seq h1 buf) (Seq.Create.create_8 v0 v1 v2 v3 v4 v5 v6 v7)


[@"substitute"]
val pupd_8: buf:huint32_p{length buf = 8} ->
  v0:uint32_t -> v1:uint32_t -> v2:uint32_t -> v3:uint32_t ->
  v4:uint32_t -> v5:uint32_t -> v6:uint32_t -> v7:uint32_t ->
  Stack unit (requires (fun h -> live h buf))
             (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                       /\ (let s = Hacl.Spec.Endianness.reveal_h32s (as_seq h1 buf) in
                         Seq.index s 0 == v0 /\ Seq.index s 1 == v1 /\ Seq.index s 2 == v2 /\ Seq.index s 3 == v3 /\
                         Seq.index s 4 == v4 /\ Seq.index s 5 == v5 /\ Seq.index s 6 == v6 /\ Seq.index s 7 == v7)))
[@"substitute"]
let pupd_8 buf v0 v1 v2 v3 v4 v5 v6 v7 =
  let h0 = u32_to_s32 v0 in
  let h1 = u32_to_s32 v1 in
  let h2 = u32_to_s32 v2 in
  let h3 = u32_to_s32 v3 in
  let h4 = u32_to_s32 v4 in
  let h5 = u32_to_s32 v5 in
  let h6 = u32_to_s32 v6 in
  let h7 = u32_to_s32 v7 in
  hupd_8 buf h0 h1 h2 h3 h4 h5 h6 h7


(* Definition of the right rotation function for UInt32.t *)
[@"substitute"]
let rotate_right (a:huint32_t) (b:uint32_t{v b <= 32}) : Tot huint32_t =
  H32.logor (H32.shift_right a b) (H32.shift_left a (U32.sub 32ul b))


val load32s_be:
  buf_32 :Buffer.buffer Hacl.UInt32.t ->
  buf_8  :Buffer.buffer Hacl.UInt8.t ->
  len_8 :FStar.UInt32.t{FStar.UInt32.v len_8 % 4 = 0 /\ FStar.UInt32.v len_8 <= length buf_8 /\ FStar.UInt32.v len_8 <= (4 * length buf_32)} ->
  Stack unit
        (requires (fun h0 -> live h0 buf_32 /\ live h0 buf_8))
        (ensures  (fun h0 _ h1 -> live h1 buf_32 /\ modifies_1 buf_32 h0 h1))

let rec load32s_be buf_32 buf_8 len_8 =
  if FStar.UInt32.(len_8 =^ 0ul) then ()
  else
    begin
      (**) assert((FStar.UInt32.v len_8 - 4) % 4 = 0);
      (**) assert(FStar.UInt32.v len_8 - 4 <= length buf_8);
      (**) assert(FStar.UInt32.v len_8 <= (4 * length buf_32));
      let x_8 = Buffer.sub buf_8 FStar.UInt32.(len_8 -^ 4ul) 4ul in
      let i_32 = len_8 /^ 4ul in
      let x_32 = Hacl.Endianness.hload32_be x_8 in
      Buffer.upd buf_32 FStar.UInt32.(i_32 -^ 1ul) x_32;
      load32s_be buf_32 buf_8 FStar.UInt32.(len_8 -^ 4ul)
    end


val store32s_be:
  buf_8  :Buffer.buffer Hacl.UInt8.t ->
  buf_32 :Buffer.buffer Hacl.UInt32.t ->
  len_32 :FStar.UInt32.t{FStar.UInt32.v len_32 * 4 <= length buf_8 /\ FStar.UInt32.v len_32 <= length buf_32} ->
  Stack unit
        (requires (fun h0 -> live h0 buf_8 /\ live h0 buf_32))
        (ensures  (fun h0 _ h1 -> live h1 buf_8 /\ modifies_1 buf_8 h0 h1))

let rec store32s_be buf_8 buf_32 len_32 =
  if FStar.UInt32.(len_32 =^ 0ul) then ()
  else
    begin
      let x_32 = Buffer.index buf_32 FStar.UInt32.(len_32 -^ 1ul) in
      let x_8 = Buffer.sub buf_8 FStar.UInt32.((len_32 -^ 1ul) *^ 4ul) 4ul in
      Hacl.Endianness.hstore32_be x_8 x_32;
      store32s_be buf_8 buf_32 FStar.UInt32.(len_32 -^ 1ul)
    end


(* [@"substitute"] *)
(* val be_bytes_of_sint32: b:huint8_p{length b >= 4} -> x:huint32_t *)
(*   -> Stack unit *)
(*           (requires (fun h -> live h b)) *)
(*           (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1)) *)

(* [@"substitute"] *)
(* let be_bytes_of_sint32 output x = *)
(*  let b0 = sint32_to_sint8 (H32.logand (H32.shift_right x 24ul) (uint32_to_sint32 255ul)) in *)
(*  let b1 = sint32_to_sint8 (H32.logand (H32.shift_right x 16ul) (uint32_to_sint32 255ul)) in *)
(*  let b2 = sint32_to_sint8 (H32.logand (H32.shift_right x 8ul)  (uint32_to_sint32 255ul)) in *)
(*  let b3 = sint32_to_sint8 (H32.logand x (uint32_to_sint32 255ul)) in *)
(*  upd output 0ul b0; *)
(*  upd output 1ul b1; *)
(*  upd output 2ul b2; *)
(*  upd output 3ul b3 *)


(* [@"substitute"] *)
(* val be_sint32_of_bytes: b:huint8_p{length b >= 4} *)
(*   -> Stack huint32_t *)
(*         (requires (fun h -> live h b)) *)
(*         (ensures (fun h0 r h1 -> live h1 b /\ modifies_1 b h0 h1)) *)

(* [@"substitute"] *)
(* let be_sint32_of_bytes b = *)
(*   let b0 = index b 0ul in *)
(*   let b1 = index b 1ul in *)
(*   let b2 = index b 2ul in *)
(*   let b3 = index b 3ul in *)
(*   let r = *)
(*     H32.add_mod (H32.add_mod (H32.add_mod (sint8_to_sint32 b3) *)
(*                                           (H32.op_Less_Less_Hat (sint8_to_sint32 b2) 8ul)) *)
(* 	                          (H32.op_Less_Less_Hat (sint8_to_sint32 b1) 16ul)) *)
(*                 (H32.op_Less_Less_Hat (sint8_to_sint32 b0) 24ul) in *)
(*   r *)


(* [@"substitute"] *)
(* val be_bytes_of_sint64: b:huint8_p{length b >= 8} -> x:huint64_t *)
(*   -> Stack unit *)
(*         (requires (fun h -> live h b)) *)
(*         (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1)) *)

(* [@"substitute"] *)
(* let be_bytes_of_sint64 output x = *)
(*  let b0 = sint64_to_sint8 (H64.logand (H64.shift_right x 56ul) (uint32_to_sint64 255ul)) in *)
(*  let b1 = sint64_to_sint8 (H64.logand (H64.shift_right x 48ul) (uint32_to_sint64 255ul)) in *)
(*  let b2 = sint64_to_sint8 (H64.logand (H64.shift_right x 40ul) (uint32_to_sint64 255ul)) in *)
(*  let b3 = sint64_to_sint8 (H64.logand (H64.shift_right x 32ul) (uint32_to_sint64 255ul)) in *)
(*  let b4 = sint64_to_sint8 (H64.logand (H64.shift_right x 24ul) (uint32_to_sint64 255ul)) in *)
(*  let b5 = sint64_to_sint8 (H64.logand (H64.shift_right x 16ul) (uint32_to_sint64 255ul)) in *)
(*  let b6 = sint64_to_sint8 (H64.logand (H64.shift_right x 8ul)  (uint32_to_sint64 255ul)) in *)
(*  let b7 = sint64_to_sint8 (H64.logand x (uint32_to_sint64 255ul)) in *)
(*  upd output 0ul b0; *)
(*  upd output 1ul b1; *)
(*  upd output 2ul b2; *)
(*  upd output 3ul b3; *)
(*  upd output 4ul b4; *)
(*  upd output 5ul b5; *)
(*  upd output 6ul b6; *)
(*  upd output 7ul b7 *)


(* val xor_bytes: *)
(*   output :huint8_p -> *)
(*   input  :huint8_p -> *)
(*   len    :uint32_t{U32.v len <= length output /\ U32.v len <= length input} -> *)
(*   Stack unit *)
(*         (requires (fun h0 -> live h0 output /\ live h0 input)) *)
(*         (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1)) *)

(* let rec xor_bytes output input len = *)
(*   if U32.(len =^ 0ul) then () *)
(*   else *)
(*     begin *)
(*       let i    = U32.(len -^ 1ul) in *)
(*       let in1i = Buffer.index input i in *)
(*       let oi   = Buffer.index output i in *)
(*       let oi   = H8.(in1i ^^ oi) in *)
(*       output.(i) <- oi; *)
(*       xor_bytes output input i *)
(*     end *)
