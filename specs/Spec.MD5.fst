module Spec.MD5

(* Source: https://tools.ietf.org/html/rfc1321 *)

open Lib.IntTypes
open Spec.Hash.Definitions

(* Section 3.3 *)

inline_for_extraction
let init_as_list : list uint32 = [
  u32 0x67452301;
  u32 0xefcdab89;
  u32 0x98badcfe;
  u32 0x10325476;
]

let init = Seq.seq_of_list init_as_list

(* Section 3.4 *)

inline_for_extraction
let f (x y z: uint32) : Tot uint32 =
  (x &. y) |. ((~. x) &. z)

inline_for_extraction
let g (x y z: uint32) : Tot uint32 =
  (x &. z) |. (y &. (~. z))

inline_for_extraction
let h (x y z: uint32) : Tot uint32 =
  x ^. y ^. z

inline_for_extraction
let i (x y z: uint32) : Tot uint32 =
  y ^. (x |. ~. z)

(* Table T: specified in 3.4, defined in Appendix A.3, function MD5Transform *)

inline_for_extraction
let t_as_list : list uint32 = [
  u32 0xd76aa478;
  u32 0xe8c7b756;
  u32 0x242070db;
  u32 0xc1bdceee;
  u32 0xf57c0faf;
  u32 0x4787c62a;
  u32 0xa8304613;
  u32 0xfd469501;
  u32 0x698098d8;
  u32 0x8b44f7af;
  u32 0xffff5bb1;
  u32 0x895cd7be;
  u32 0x6b901122;
  u32 0xfd987193;
  u32 0xa679438e;
  u32 0x49b40821;

  u32 0xf61e2562;
  u32 0xc040b340;
  u32 0x265e5a51;
  u32 0xe9b6c7aa;
  u32 0xd62f105d;
  u32 0x02441453;
  u32 0xd8a1e681;
  u32 0xe7d3fbc8;
  u32 0x21e1cde6;
  u32 0xc33707d6;
  u32 0xf4d50d87;
  u32 0x455a14ed;
  u32 0xa9e3e905;
  u32 0xfcefa3f8;
  u32 0x676f02d9;
  u32 0x8d2a4c8a;

  u32 0xfffa3942;
  u32 0x8771f681;
  u32 0x6d9d6122;
  u32 0xfde5380c;
  u32 0xa4beea44;
  u32 0x4bdecfa9;
  u32 0xf6bb4b60;
  u32 0xbebfbc70;
  u32 0x289b7ec6;
  u32 0xeaa127fa;
  u32 0xd4ef3085;
  u32 0x4881d05;
  u32 0xd9d4d039;
  u32 0xe6db99e5;
  u32 0x1fa27cf8;
  u32 0xc4ac5665;

  u32 0xf4292244;
  u32 0x432aff97;
  u32 0xab9423a7;
  u32 0xfc93a039;
  u32 0x655b59c3;
  u32 0x8f0ccc92;
  u32 0xffeff47d;
  u32 0x85845dd1;
  u32 0x6fa87e4f;
  u32 0xfe2ce6e0;
  u32 0xa3014314;
  u32 0x4e0811a1;
  u32 0xf7537e82;
  u32 0xbd3af235;
  u32 0x2ad7d2bb;
  u32 0xeb86d391;
]

module L = FStar.List.Tot

let t : Seq.lseq uint32 64 =
  assert_norm (L.length t_as_list == 64);
  Seq.seq_of_list t_as_list

let abcd_idx = (n: nat { n < 4 } )

let abcd_t = Seq.lseq uint32 4

let x_idx = (n: nat { n < 16 } )
let x_t = Seq.lseq uint32 16

let t_idx = (n: nat { 1 <= n /\ n <= 64 } )

inline_for_extraction
let rotate_idx = rotval U32

let round_op_gen_aux (f: (uint32 -> uint32 -> uint32 -> Tot uint32)) (abcd: abcd_t) (x: x_t) (a b c d: abcd_idx) (k: x_idx) (s: rotate_idx) (i: t_idx) : Tot abcd_t =
  let va = Seq.index abcd a in
  let vb = Seq.index abcd b in
  let vc = Seq.index abcd c in
  let vd = Seq.index abcd d in
  Seq.upd abcd a (vb +. ((va +. f vb vc vd +. Seq.index x k +. Seq.index t (i - 1)) <<<. s))

[@"opaque_to_smt"]
let round_op_gen = round_op_gen_aux

(* Round 1 *)

let round1_op = round_op_gen f

let ia : abcd_idx = 0
let ib : abcd_idx = 1
let ic : abcd_idx = 2
let id : abcd_idx = 3

let round1_aux (abcd: abcd_t) (x: x_t) : Tot abcd_t =
  let abcd = round1_op abcd x ia ib ic id  0  7ul  1 in
  let abcd = round1_op abcd x id ia ib ic  1 12ul  2 in
  let abcd = round1_op abcd x ic id ia ib  2 17ul  3 in
  let abcd = round1_op abcd x ib ic id ia  3 22ul  4 in

  let abcd = round1_op abcd x ia ib ic id 4 7ul 5 in
  let abcd = round1_op abcd x id ia ib ic 5 12ul 6 in
  let abcd = round1_op abcd x ic id ia ib 6 17ul 7 in
  let abcd = round1_op abcd x ib ic id ia 7 22ul 8 in

  let abcd = round1_op abcd x ia ib ic id 8 7ul 9 in
  let abcd = round1_op abcd x id ia ib ic 9 12ul 10 in
  let abcd = round1_op abcd x ic id ia ib 10 17ul 11 in
  let abcd = round1_op abcd x ib ic id ia 11 22ul 12 in

  let abcd = round1_op abcd x ia ib ic id 12 7ul 13 in
  let abcd = round1_op abcd x id ia ib ic 13 12ul 14 in
  let abcd = round1_op abcd x ic id ia ib 14 17ul 15 in
  let abcd = round1_op abcd x ib ic id ia 15 22ul 16 in

  abcd

[@"opaque_to_smt"]
let round1 = round1_aux

let round2_op = round_op_gen g

let round2_aux (abcd: abcd_t) (x: x_t) : Tot abcd_t =
  let abcd = round2_op abcd x ia ib ic id 1 5ul 17 in
  let abcd = round2_op abcd x id ia ib ic 6 9ul 18 in
  let abcd = round2_op abcd x ic id ia ib 11 14ul 19 in
  let abcd = round2_op abcd x ib ic id ia 0 20ul 20 in

  let abcd = round2_op abcd x ia ib ic id 5 5ul 21 in
  let abcd = round2_op abcd x id ia ib ic 10 9ul 22 in
  let abcd = round2_op abcd x ic id ia ib 15 14ul 23 in
  let abcd = round2_op abcd x ib ic id ia 4 20ul 24 in

  let abcd = round2_op abcd x ia ib ic id 9 5ul 25 in
  let abcd = round2_op abcd x id ia ib ic 14 9ul 26 in
  let abcd = round2_op abcd x ic id ia ib 3 14ul 27 in
  let abcd = round2_op abcd x ib ic id ia 8 20ul 28 in

  let abcd = round2_op abcd x ia ib ic id 13 5ul 29 in
  let abcd = round2_op abcd x id ia ib ic 2 9ul 30 in
  let abcd = round2_op abcd x ic id ia ib 7 14ul 31 in
  let abcd = round2_op abcd x ib ic id ia 12 20ul 32 in

  abcd

[@"opaque_to_smt"]
let round2 = round2_aux

let round3_op = round_op_gen h

let round3_aux (abcd: abcd_t) (x: x_t) : Tot abcd_t =
  let abcd = round3_op abcd x ia ib ic id 5 4ul 33 in
  let abcd = round3_op abcd x id ia ib ic 8 11ul 34 in
  let abcd = round3_op abcd x ic id ia ib 11 16ul 35 in
  let abcd = round3_op abcd x ib ic id ia 14 23ul 36 in

  let abcd = round3_op abcd x ia ib ic id 1 4ul 37 in
  let abcd = round3_op abcd x id ia ib ic 4 11ul 38 in
  let abcd = round3_op abcd x ic id ia ib 7 16ul 39 in
  let abcd = round3_op abcd x ib ic id ia 10 23ul 40 in

  let abcd = round3_op abcd x ia ib ic id 13 4ul 41 in
  let abcd = round3_op abcd x id ia ib ic 0 11ul 42 in
  let abcd = round3_op abcd x ic id ia ib 3 16ul 43 in
  let abcd = round3_op abcd x ib ic id ia 6 23ul 44 in

  let abcd = round3_op abcd x ia ib ic id 9 4ul 45 in
  let abcd = round3_op abcd x id ia ib ic 12 11ul 46 in
  let abcd = round3_op abcd x ic id ia ib 15 16ul 47 in
  let abcd = round3_op abcd x ib ic id ia 2 23ul 48 in

  abcd

[@"opaque_to_smt"]
let round3 = round3_aux

let round4_op = round_op_gen i

let round4_aux (abcd: abcd_t) (x: x_t) : Tot abcd_t =
  let abcd = round4_op abcd x ia ib ic id 0 6ul 49 in
  let abcd = round4_op abcd x id ia ib ic 7 10ul 50 in
  let abcd = round4_op abcd x ic id ia ib 14 15ul 51 in
  let abcd = round4_op abcd x ib ic id ia 5 21ul 52 in

  let abcd = round4_op abcd x ia ib ic id 12 6ul 53 in
  let abcd = round4_op abcd x id ia ib ic 3 10ul 54 in
  let abcd = round4_op abcd x ic id ia ib 10 15ul 55 in
  let abcd = round4_op abcd x ib ic id ia 1 21ul 56 in

  let abcd = round4_op abcd x ia ib ic id 8 6ul 57 in
  let abcd = round4_op abcd x id ia ib ic 15 10ul 58 in
  let abcd = round4_op abcd x ic id ia ib 6 15ul 59 in
  let abcd = round4_op abcd x ib ic id ia 13 21ul 60 in

  let abcd = round4_op abcd x ia ib ic id 4 6ul 61 in
  let abcd = round4_op abcd x id ia ib ic 11 10ul 62 in
  let abcd = round4_op abcd x ic id ia ib 2 15ul 63 in
  let abcd = round4_op abcd x ib ic id ia 9 21ul 64 in

  abcd

[@"opaque_to_smt"]
let round4 = round4_aux

let rounds_aux (abcd: abcd_t) (x: x_t) : Tot abcd_t =
  let abcd = round1 abcd x in
  let abcd = round2 abcd x in
  let abcd = round3 abcd x in
  let abcd = round4 abcd x in
  abcd

[@"opaque_to_smt"]
let rounds = rounds_aux

let overwrite_aux (abcd: abcd_t) (a' b' c' d' : uint32) : Tot abcd_t =
  let abcd : abcd_t = Seq.upd abcd ia a' in
  let abcd : abcd_t = Seq.upd abcd ib b' in
  let abcd : abcd_t = Seq.upd abcd ic c' in
  let abcd : abcd_t = Seq.upd abcd id d' in
  abcd

[@"opaque_to_smt"]
let overwrite = overwrite_aux

let update_aux abcd x =
  let x = words_of_bytes MD5 #16 x in
  let aa = Seq.index abcd ia in
  let bb = Seq.index abcd ib in
  let cc = Seq.index abcd ic in
  let dd = Seq.index abcd id in
//  let aabbccdd = abcd in
  let abcd = rounds abcd x in
  overwrite abcd
    (Seq.index abcd ia +. aa)
    (Seq.index abcd ib +. bb)
    (Seq.index abcd ic +. cc)
    (Seq.index abcd id +. dd)

[@"opaque_to_smt"]
let update = update_aux

(* Sections 3.1 and 3.2 *)

let pad = Spec.Hash.PadFinish.pad MD5

(* Section 3.5 *)

let finish = Spec.Hash.PadFinish.finish MD5

