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


#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"


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
val aux_hupd_16: buf:huint32_p{length buf = 16} ->
  v0:H32.t -> v1:H32.t -> v2:H32.t -> v3:H32.t -> v4:H32.t -> v5:H32.t -> v6:H32.t -> v7:H32.t ->
  v8:H32.t -> v9:H32.t -> v10:H32.t -> v11:H32.t -> v12:H32.t -> v13:H32.t -> v14:H32.t -> v15:H32.t ->
  Stack unit (requires (fun h -> live h buf))
             (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                         /\ (let s = as_seq h1 buf in
                         Seq.index s 0 == v0 /\ Seq.index s 1 == v1 /\ Seq.index s 2 == v2 /\ Seq.index s 3 == v3 /\
                         Seq.index s 4 == v4 /\ Seq.index s 5 == v5 /\ Seq.index s 6 == v6 /\ Seq.index s 7 == v7 /\
                         Seq.index s 8 == v8 /\ Seq.index s 9 == v9 /\ Seq.index s 10 == v10 /\ Seq.index s 11 == v11 /\
                         Seq.index s 12 == v12 /\ Seq.index s 13 == v13 /\ Seq.index s 14 == v14 /\ Seq.index s 15 == v15)))

[@"substitute"]
let aux_hupd_16 buf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
  let p1 = Buffer.sub buf 0ul 8ul in
  let p2 = Buffer.sub buf 8ul 8ul in
  hupd_8 p1 v0 v1 v2 v3 v4 v5 v6 v7;
  hupd_8 p2 v8 v9 v10 v11 v12 v13 v14 v15


[@"substitute"]
val hupd_16: buf:huint32_p{length buf = 16} ->
  v0:H32.t -> v1:H32.t -> v2:H32.t -> v3:H32.t -> v4:H32.t -> v5:H32.t -> v6:H32.t -> v7:H32.t ->
  v8:H32.t -> v9:H32.t -> v10:H32.t -> v11:H32.t -> v12:H32.t -> v13:H32.t -> v14:H32.t -> v15:H32.t ->
  Stack unit (requires (fun h -> live h buf))
             (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                         /\ (let s = as_seq h1 buf in
                         Seq.Create.create_16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 == s)))

[@"substitute"]
let hupd_16 buf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
  aux_hupd_16 buf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15;
  let h1 = ST.get () in
  Seq.lemma_eq_intro (as_seq h1 buf) (Seq.Create.create_16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)


#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"


[@"substitute"]
val aux_hupd_64: buf:huint32_p{length buf = 64} ->
  v0:H32.t -> v1:H32.t -> v2:H32.t -> v3:H32.t -> v4:H32.t -> v5:H32.t -> v6:H32.t -> v7:H32.t ->
  v8:H32.t -> v9:H32.t ->
  v10:H32.t -> v11:H32.t -> v12:H32.t -> v13:H32.t -> v14:H32.t -> v15:H32.t -> v16:H32.t -> v17:H32.t ->
  v18:H32.t -> v19:H32.t ->
  v20:H32.t -> v21:H32.t -> v22:H32.t -> v23:H32.t -> v24:H32.t -> v25:H32.t -> v26:H32.t -> v27:H32.t ->
  v28:H32.t -> v29:H32.t ->
  v30:H32.t -> v31:H32.t -> v32:H32.t -> v33:H32.t -> v34:H32.t -> v35:H32.t -> v36:H32.t -> v37:H32.t ->
  v38:H32.t -> v39:H32.t ->
  v40:H32.t -> v41:H32.t -> v42:H32.t -> v43:H32.t -> v44:H32.t -> v45:H32.t -> v46:H32.t -> v47:H32.t ->
  v48:H32.t -> v49:H32.t ->
  v50:H32.t -> v51:H32.t -> v52:H32.t -> v53:H32.t -> v54:H32.t -> v55:H32.t -> v56:H32.t -> v57:H32.t ->
  v58:H32.t -> v59:H32.t ->
  v60:H32.t -> v61:H32.t -> v62:H32.t -> v63:H32.t ->
  Stack unit (requires (fun h -> live h buf))
             (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                         /\ (let s = as_seq h1 buf in
                           Seq.index s 0 == v0 /\ Seq.index s 1 == v1 /\ Seq.index s 2 == v2 /\ Seq.index s 3 == v3
                         /\ Seq.index s 4 == v4 /\ Seq.index s 5 == v5 /\ Seq.index s 6 == v6 /\ Seq.index s 7 == v7
                         /\ Seq.index s 8 == v8 /\ Seq.index s 9 == v9
                         /\ Seq.index s 10 == v10 /\ Seq.index s 11 == v11 /\ Seq.index s 12 == v12 /\ Seq.index s 13 == v13
                         /\ Seq.index s 14 == v14 /\ Seq.index s 15 == v15 /\ Seq.index s 16 == v16 /\ Seq.index s 17 == v17
                         /\ Seq.index s 18 == v18 /\ Seq.index s 19 == v19
                         /\ Seq.index s 20 == v20 /\ Seq.index s 21 == v21 /\ Seq.index s 22 == v22 /\ Seq.index s 23 == v23
                         /\ Seq.index s 24 == v24 /\ Seq.index s 25 == v25 /\ Seq.index s 26 == v26 /\ Seq.index s 27 == v27
                         /\ Seq.index s 28 == v28 /\ Seq.index s 29 == v29
                         /\ Seq.index s 30 == v30 /\ Seq.index s 31 == v31 /\ Seq.index s 32 == v32 /\ Seq.index s 33 == v33
                         /\ Seq.index s 34 == v34 /\ Seq.index s 35 == v35 /\ Seq.index s 36 == v36 /\ Seq.index s 37 == v37
                         /\ Seq.index s 38 == v38 /\ Seq.index s 39 == v39
                         /\ Seq.index s 40 == v40 /\ Seq.index s 41 == v41 /\ Seq.index s 42 == v42 /\ Seq.index s 43 == v43
                         /\ Seq.index s 44 == v44 /\ Seq.index s 45 == v45 /\ Seq.index s 46 == v46 /\ Seq.index s 47 == v47
                         /\ Seq.index s 48 == v48 /\ Seq.index s 49 == v49
                         /\ Seq.index s 50 == v50 /\ Seq.index s 51 == v51 /\ Seq.index s 52 == v52 /\ Seq.index s 53 == v53
                         /\ Seq.index s 54 == v54 /\ Seq.index s 55 == v55 /\ Seq.index s 56 == v56 /\ Seq.index s 57 == v57
                         /\ Seq.index s 58 == v58 /\ Seq.index s 59 == v59
                         /\ Seq.index s 60 == v60 /\ Seq.index s 61 == v61 /\ Seq.index s 62 == v62 /\ Seq.index s 63 == v63)))

[@"substitute"]
let aux_hupd_64 buf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 =
  let p1 = Buffer.sub buf 0ul 16ul in
  let p2 = Buffer.sub buf 16ul 16ul in
  let p3 = Buffer.sub buf 32ul 16ul in
  let p4 = Buffer.sub buf 48ul 16ul in
  hupd_16 p1 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15;
  hupd_16 p2 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31;
  hupd_16 p3 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47;
  hupd_16 p4 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63


[@"substitute"]
val hupd_64: buf:huint32_p{length buf = 64} ->
  v0:H32.t -> v1:H32.t -> v2:H32.t -> v3:H32.t -> v4:H32.t -> v5:H32.t -> v6:H32.t -> v7:H32.t ->
  v8:H32.t -> v9:H32.t ->
  v10:H32.t -> v11:H32.t -> v12:H32.t -> v13:H32.t -> v14:H32.t -> v15:H32.t -> v16:H32.t -> v17:H32.t ->
  v18:H32.t -> v19:H32.t ->
  v20:H32.t -> v21:H32.t -> v22:H32.t -> v23:H32.t -> v24:H32.t -> v25:H32.t -> v26:H32.t -> v27:H32.t ->
  v28:H32.t -> v29:H32.t ->
  v30:H32.t -> v31:H32.t -> v32:H32.t -> v33:H32.t -> v34:H32.t -> v35:H32.t -> v36:H32.t -> v37:H32.t ->
  v38:H32.t -> v39:H32.t ->
  v40:H32.t -> v41:H32.t -> v42:H32.t -> v43:H32.t -> v44:H32.t -> v45:H32.t -> v46:H32.t -> v47:H32.t ->
  v48:H32.t -> v49:H32.t ->
  v50:H32.t -> v51:H32.t -> v52:H32.t -> v53:H32.t -> v54:H32.t -> v55:H32.t -> v56:H32.t -> v57:H32.t ->
  v58:H32.t -> v59:H32.t ->
  v60:H32.t -> v61:H32.t -> v62:H32.t -> v63:H32.t ->
  Stack unit (requires (fun h -> live h buf))
             (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                         /\ (let s = as_seq h1 buf in
                         Seq.Create.create_64  v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 == s)))

[@"substitute"]
let hupd_64 buf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 =
  aux_hupd_64 buf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63;
  let h1 = ST.get () in
  Seq.lemma_eq_intro (as_seq h1 buf) (Seq.Create.create_64 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63)


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
  buf_8  :Buffer.buffer Hacl.UInt8.t {length buf_8 = 4 * length buf_32} ->
  len_8 :FStar.UInt32.t{v len_8 = length buf_8} ->
  Stack unit
        (requires (fun h0 -> live h0 buf_32 /\ live h0 buf_8))
        (ensures  (fun h0 _ h1 -> live h0 buf_32 /\ live h0 buf_8 /\ live h1 buf_32 /\ modifies_1 buf_32 h0 h1
                  /\ (as_seq h1 buf_32 == Spec.Lib.uint32s_from_be (length buf_32) (as_seq h0 buf_8))))

let rec load32s_be buf_32 buf_8 len_8 =
  admit();
  if FStar.UInt32.(len_8 =^ 0ul) then ()
  else
    begin
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
