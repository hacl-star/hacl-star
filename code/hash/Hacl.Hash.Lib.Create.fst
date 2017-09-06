module Hacl.Hash.Lib.Create

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer

open Hacl.Spec.Endianness

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

let uint8_ht  = Hacl.UInt8.t
let uint32_ht = Hacl.UInt32.t
let uint64_ht = Hacl.UInt64.t

let uint8_p  = Buffer.buffer uint8_ht
let uint32_p = Buffer.buffer uint32_ht
let uint64_p = Buffer.buffer uint64_ht


(* Definitions of aliases for functions *)
inline_for_extraction let u8_to_s8 = Cast.uint8_to_sint8
inline_for_extraction let u32_to_s32 = Cast.uint32_to_sint32
inline_for_extraction let u32_to_s64 = Cast.uint32_to_sint64
inline_for_extraction let s32_to_s8  = Cast.sint32_to_sint8
inline_for_extraction let s32_to_s64 = Cast.sint32_to_sint64
inline_for_extraction let u64_to_s64 = Cast.uint64_to_sint64



#reset-options "--max_fuel 0 --z3rlimit 200"

[@"substitute"]
val hupd_4: buf:uint32_p{length buf = 4} ->
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
private val aux_hupd_8: buf:uint32_p{length buf = 8} ->
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
val hupd_8: buf:uint32_p{length buf = 8} ->
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
private val aux_hupd_16: buf:uint32_p{length buf = 16} ->
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
val hupd_16: buf:uint32_p{length buf = 16} ->
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


[@"substitute"]
private val aux_hupd_64: buf:uint32_p{length buf = 64} ->
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
val hupd_64: buf:uint32_p{length buf = 64} ->
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
val hupd64_4: buf:uint64_p{length buf = 4} ->
  v0:H64.t -> v1:H64.t -> v2:H64.t -> v3:H64.t ->
  Stack unit (requires (fun h -> live h buf))
             (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                         /\ (let s = as_seq h1 buf in
                         Seq.index s 0 == v0 /\ Seq.index s 1 == v1 /\ Seq.index s 2 == v2 /\ Seq.index s 3 == v3)))

[@"substitute"]
let hupd64_4 buf v0 v1 v2 v3 =
  buf.(0ul) <- v0;
  buf.(1ul) <- v1;
  buf.(2ul) <- v2;
  buf.(3ul) <- v3


[@"substitute"]
private val aux_hupd64_8: buf:uint64_p{length buf = 8} ->
  v0:H64.t -> v1:H64.t -> v2:H64.t -> v3:H64.t -> v4:H64.t -> v5:H64.t -> v6:H64.t -> v7:H64.t ->
  Stack unit (requires (fun h -> live h buf))
             (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                         /\ (let s = as_seq h1 buf in
                         Seq.index s 0 == v0 /\ Seq.index s 1 == v1 /\ Seq.index s 2 == v2 /\ Seq.index s 3 == v3 /\
                         Seq.index s 4 == v4 /\ Seq.index s 5 == v5 /\ Seq.index s 6 == v6 /\ Seq.index s 7 == v7)))

[@"substitute"]
let aux_hupd64_8 buf v0 v1 v2 v3 v4 v5 v6 v7 =
  let p1 = Buffer.sub buf 0ul 4ul in
  let p2 = Buffer.sub buf 4ul 4ul in
  hupd64_4 p1 v0 v1 v2 v3;
  hupd64_4 p2 v4 v5 v6 v7


[@"substitute"]
val hupd64_8: buf:uint64_p{length buf = 8} ->
  v0:H64.t -> v1:H64.t -> v2:H64.t -> v3:H64.t -> v4:H64.t -> v5:H64.t -> v6:H64.t -> v7:H64.t ->
  Stack unit (requires (fun h -> live h buf))
             (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                         /\ (let s = as_seq h1 buf in Seq.Create.create_8 v0 v1 v2 v3 v4 v5 v6 v7 == s)))

[@"substitute"]
let hupd64_8 buf v0 v1 v2 v3 v4 v5 v6 v7 =
  aux_hupd64_8 buf v0 v1 v2 v3 v4 v5 v6 v7;
  let h1 = ST.get () in
  Seq.lemma_eq_intro (as_seq h1 buf) (Seq.Create.create_8 v0 v1 v2 v3 v4 v5 v6 v7)


[@"substitute"]
private val aux_hupd64_16: buf:uint64_p{length buf = 16} ->
  v0:H64.t -> v1:H64.t -> v2:H64.t -> v3:H64.t -> v4:H64.t -> v5:H64.t -> v6:H64.t -> v7:H64.t ->
  v8:H64.t -> v9:H64.t -> v10:H64.t -> v11:H64.t -> v12:H64.t -> v13:H64.t -> v14:H64.t -> v15:H64.t ->
  Stack unit (requires (fun h -> live h buf))
             (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                         /\ (let s = as_seq h1 buf in
                         Seq.index s 0 == v0 /\ Seq.index s 1 == v1 /\ Seq.index s 2 == v2 /\ Seq.index s 3 == v3 /\
                         Seq.index s 4 == v4 /\ Seq.index s 5 == v5 /\ Seq.index s 6 == v6 /\ Seq.index s 7 == v7 /\
                         Seq.index s 8 == v8 /\ Seq.index s 9 == v9 /\ Seq.index s 10 == v10 /\ Seq.index s 11 == v11 /\
                         Seq.index s 12 == v12 /\ Seq.index s 13 == v13 /\ Seq.index s 14 == v14 /\ Seq.index s 15 == v15)))

[@"substitute"]
let aux_hupd64_16 buf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
  let p1 = Buffer.sub buf 0ul 8ul in
  let p2 = Buffer.sub buf 8ul 8ul in
  hupd64_8 p1 v0 v1 v2 v3 v4 v5 v6 v7;
  hupd64_8 p2 v8 v9 v10 v11 v12 v13 v14 v15


[@"substitute"]
val hupd64_16: buf:uint64_p{length buf = 16} ->
  v0:H64.t -> v1:H64.t -> v2:H64.t -> v3:H64.t -> v4:H64.t -> v5:H64.t -> v6:H64.t -> v7:H64.t ->
  v8:H64.t -> v9:H64.t -> v10:H64.t -> v11:H64.t -> v12:H64.t -> v13:H64.t -> v14:H64.t -> v15:H64.t ->
  Stack unit (requires (fun h -> live h buf))
             (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                         /\ (let s = as_seq h1 buf in
                         Seq.Create.create_16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 == s)))

[@"substitute"]
let hupd64_16 buf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
  aux_hupd64_16 buf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15;
  let h1 = ST.get () in
  Seq.lemma_eq_intro (as_seq h1 buf) (Seq.Create.create_16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)


 [@"substitute"]
private val aux_hupd64_80: buf:uint64_p{length buf = 80} ->
  v0:H64.t -> v1:H64.t -> v2:H64.t -> v3:H64.t -> v4:H64.t -> v5:H64.t -> v6:H64.t -> v7:H64.t ->
  v8:H64.t -> v9:H64.t ->
  v10:H64.t -> v11:H64.t -> v12:H64.t -> v13:H64.t -> v14:H64.t -> v15:H64.t -> v16:H64.t -> v17:H64.t ->
  v18:H64.t -> v19:H64.t ->
  v20:H64.t -> v21:H64.t -> v22:H64.t -> v23:H64.t -> v24:H64.t -> v25:H64.t -> v26:H64.t -> v27:H64.t ->
  v28:H64.t -> v29:H64.t ->
  v30:H64.t -> v31:H64.t -> v32:H64.t -> v33:H64.t -> v34:H64.t -> v35:H64.t -> v36:H64.t -> v37:H64.t ->
  v38:H64.t -> v39:H64.t ->
  v40:H64.t -> v41:H64.t -> v42:H64.t -> v43:H64.t -> v44:H64.t -> v45:H64.t -> v46:H64.t -> v47:H64.t ->
  v48:H64.t -> v49:H64.t ->
  v50:H64.t -> v51:H64.t -> v52:H64.t -> v53:H64.t -> v54:H64.t -> v55:H64.t -> v56:H64.t -> v57:H64.t ->
  v58:H64.t -> v59:H64.t ->
  v60:H64.t -> v61:H64.t -> v62:H64.t -> v63:H64.t -> v64:H64.t -> v65:H64.t -> v66:H64.t -> v67:H64.t ->
  v68:H64.t -> v69:H64.t ->
  v70:H64.t -> v71:H64.t -> v72:H64.t -> v73:H64.t -> v74:H64.t -> v75:H64.t -> v76:H64.t -> v77:H64.t ->
  v78:H64.t -> v79:H64.t ->
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
                         /\ Seq.index s 60 == v60 /\ Seq.index s 61 == v61 /\ Seq.index s 62 == v62 /\ Seq.index s 63 == v63
                         /\ Seq.index s 64 == v64 /\ Seq.index s 65 == v65 /\ Seq.index s 66 == v66 /\ Seq.index s 67 == v67
                         /\ Seq.index s 68 == v68 /\ Seq.index s 69 == v69
                         /\ Seq.index s 70 == v70 /\ Seq.index s 71 == v71 /\ Seq.index s 72 == v72 /\ Seq.index s 73 == v73
                         /\ Seq.index s 74 == v74 /\ Seq.index s 75 == v75 /\ Seq.index s 76 == v76 /\ Seq.index s 77 == v77
                         /\ Seq.index s 78 == v78 /\ Seq.index s 79 == v79)))

[@"substitute"]
let aux_hupd64_80 buf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 =
  let p1 = Buffer.sub buf 0ul 16ul in
  let p2 = Buffer.sub buf 16ul 16ul in
  let p3 = Buffer.sub buf 32ul 16ul in
  let p4 = Buffer.sub buf 48ul 16ul in
  let p5 = Buffer.sub buf 64ul 16ul in
  hupd64_16 p1 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15;
  hupd64_16 p2 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31;
  hupd64_16 p3 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47;
  hupd64_16 p4 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63;
  hupd64_16 p5 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79


#reset-options "--max_fuel 0 --z3rlimit 25"

[@"substitute"]
val hupd64_80: buf:uint64_p{length buf = 80} ->
  v0:H64.t -> v1:H64.t -> v2:H64.t -> v3:H64.t -> v4:H64.t -> v5:H64.t -> v6:H64.t -> v7:H64.t ->
  v8:H64.t -> v9:H64.t ->
  v10:H64.t -> v11:H64.t -> v12:H64.t -> v13:H64.t -> v14:H64.t -> v15:H64.t -> v16:H64.t -> v17:H64.t ->
  v18:H64.t -> v19:H64.t ->
  v20:H64.t -> v21:H64.t -> v22:H64.t -> v23:H64.t -> v24:H64.t -> v25:H64.t -> v26:H64.t -> v27:H64.t ->
  v28:H64.t -> v29:H64.t ->
  v30:H64.t -> v31:H64.t -> v32:H64.t -> v33:H64.t -> v34:H64.t -> v35:H64.t -> v36:H64.t -> v37:H64.t ->
  v38:H64.t -> v39:H64.t ->
  v40:H64.t -> v41:H64.t -> v42:H64.t -> v43:H64.t -> v44:H64.t -> v45:H64.t -> v46:H64.t -> v47:H64.t ->
  v48:H64.t -> v49:H64.t ->
  v50:H64.t -> v51:H64.t -> v52:H64.t -> v53:H64.t -> v54:H64.t -> v55:H64.t -> v56:H64.t -> v57:H64.t ->
  v58:H64.t -> v59:H64.t ->
  v60:H64.t -> v61:H64.t -> v62:H64.t -> v63:H64.t -> v64:H64.t -> v65:H64.t -> v66:H64.t -> v67:H64.t ->
  v68:H64.t -> v69:H64.t ->
  v70:H64.t -> v71:H64.t -> v72:H64.t -> v73:H64.t -> v74:H64.t -> v75:H64.t -> v76:H64.t -> v77:H64.t ->
  v78:H64.t -> v79:H64.t ->
  Stack unit (requires (fun h -> live h buf))
             (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1
                         /\ (let s = as_seq h1 buf in
                         Seq.Create.create_80  v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 == s)))

[@"substitute"]
let hupd64_80 buf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63  v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 =
  aux_hupd64_80 buf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79;
  let h1 = ST.get () in
  Seq.lemma_eq_intro (as_seq h1 buf) (Seq.Create.create_80 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79)
