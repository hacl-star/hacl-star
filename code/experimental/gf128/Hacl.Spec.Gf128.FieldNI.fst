module Hacl.Spec.Gf128.FieldNI

open FStar.Mul

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence

module S = Spec.GF128
module GF = Spec.GaloisField
module Vec = Hacl.Spec.GF128.Vec

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let vec128 = vec_t U128 1

inline_for_extraction noextract
let to_elem (s:vec128) : S.elem =
  (vec_v s).[0]

inline_for_extraction noextract
let to_elem4 (x1:vec128) (x2:vec128) (x3:vec128) (x4:vec128) : Vec.elem4 =
  create4 (vec_v x1).[0] (vec_v x2).[0] (vec_v x3).[0] (vec_v x4).[0]


inline_for_extraction
let cl_add (x:vec128) (y:vec128) : Tot vec128 = vec_xor x y


inline_for_extraction
let clmul_wide (x:vec128) (y:vec128) : Tot (vec128 & vec128) =
  let lo = vec_clmul_lo_lo x y in
  let m1 = vec_clmul_hi_lo x y in
  let m2 = vec_clmul_lo_hi x y in
  let hi = vec_clmul_hi_hi x y in
  let m1 = cl_add m1 m2 in
  let m2 = vec_shift_left m1 (size 64) in
  let m1 = vec_shift_right m1 (size 64) in
  let lo = cl_add lo m2 in
  let hi = cl_add hi m1 in
  (hi,lo)


inline_for_extraction
let clmul_wide4
  (x1:vec128) (x2:vec128) (x3:vec128) (x4:vec128)
  (y1:vec128) (y2:vec128) (y3:vec128) (y4:vec128): Tot (vec128 & vec128) =

  let lo1 = vec_clmul_lo_lo x1 y1 in
  let lo2 = vec_clmul_lo_lo x2 y2 in
  let lo3 = vec_clmul_lo_lo x3 y3 in
  let lo4 = vec_clmul_lo_lo x4 y4 in
  let lo = cl_add lo1 lo2 in
  let lo = cl_add lo lo3 in
  let lo = cl_add lo lo4 in

  let m1 = vec_clmul_hi_lo x1 y1 in
  let m2 = vec_clmul_hi_lo x2 y2 in
  let m3 = vec_clmul_hi_lo x3 y3 in
  let m4 = vec_clmul_hi_lo x4 y4 in
  let m = cl_add m1 m2 in
  let m = cl_add m m3 in
  let m = cl_add m m4 in

  let m1 = vec_clmul_lo_hi x1 y1 in
  let m2 = vec_clmul_lo_hi x2 y2 in
  let m3 = vec_clmul_lo_hi x3 y3 in
  let m4 = vec_clmul_lo_hi x4 y4 in
  let m = cl_add m m1 in
  let m = cl_add m m2 in
  let m = cl_add m m3 in
  let m = cl_add m m4 in

  let hi1 = vec_clmul_hi_hi x1 y1 in
  let hi2 = vec_clmul_hi_hi x2 y2 in
  let hi3 = vec_clmul_hi_hi x3 y3 in
  let hi4 = vec_clmul_hi_hi x4 y4 in
  let hi = cl_add hi1 hi2 in
  let hi = cl_add hi hi3 in
  let hi = cl_add hi hi4 in

  let m1 = vec_shift_left m (size 64) in
  let m2 = vec_shift_right m (size 64) in
  let lo = cl_add lo m1 in
  let hi = cl_add hi m2 in
  (hi, lo)


// inline_for_extraction
// let vec128_shift_left_bits (x:vec128) (y:size_t): Tot vec128 =
//   if (y %. size 8 =. size 0) then
//     vec128_shift_left x y
//   else if (y <. size 64) then
//     let x1 = vec128_shift_right64 x (size 64 -. y) in
//     let x2 = vec128_shift_left64 x y in
//     let x3 = vec128_shift_left x1 (size 64) in
//     let x4 = vec128_or x3 x2 in
//     x4
//   else
//     let x1 = vec128_shift_left64 x (y -. size 64) in
//     let x2 = vec128_shift_left x1 (size 64) in
//     x2


// inline_for_extraction
// let vec128_shift_right_bits (x:vec128) (y:size_t) : Tot vec128 =
//   if (y %. size 8 =. size 0) then
//     vec128_shift_right x y
//   else if (y <. size 64) then
//     let x1 = vec128_shift_left64 x (size 64 -. y) in
//     let x2 = vec128_shift_right64 x y in
//     let x3 = vec128_shift_right x1 (size 64) in
//     let x4 = vec128_or x3 x2 in
//     x4
//   else
//     let x1 = vec128_shift_right64 x (y -. size 64) in
//     let x2 = vec128_shift_right x1 (size 64) in
//     x2


inline_for_extraction
let gf128_reduce (hi:vec128) (lo:vec128) : Tot vec128 =
  (* LEFT SHIFT [hi:lo] by 1 *)
  let lo1 = cast U128 1 (vec_shift_right (cast U64 2 lo) (size 63)) in
  let lo2 = vec_shift_left lo1 (size 64) in
  let lo3 = cast U128 1 (vec_shift_left (cast U64 2 lo) (size 1)) in
  let lo3 = vec_xor lo3 lo2 in

  let hi1 = cast U128 1 (vec_shift_right (cast U64 2 hi) (size 63)) in
  let hi1 = vec_shift_left hi1 (size 64) in
  let hi2 = cast U128 1 (vec_shift_left (cast U64 2 hi) (size 1)) in
  let hi2 = vec_xor hi2 hi1 in

  let lo1 = cast U128 1 (vec_shift_right (cast U64 2 lo) (size 63)) in
  let lo1 = vec_shift_right lo1 (size 64) in
  let hi2 = vec_xor hi2 lo1 in

  let lo = lo3 in
  let hi = hi2 in
(*
    let lo1 = vec128_shift_right_bits lo (size 127) in
    let lo = vec128_shift_left_bits lo (size 1) in
    let hi = vec128_shift_left_bits hi (size 1) in
    let hi = vec128_xor hi lo1 in
*)
  (* LEFT SHIFT [x0:0] BY 63,62,57 and xor with [x1:x0] *)
  let lo1 = cast U128 1 (vec_shift_left (cast U64 2 lo) (size 63)) in
  let lo2 = cast U128 1 (vec_shift_left (cast U64 2 lo) (size 62)) in
  let lo3 = cast U128 1 (vec_shift_left (cast U64 2 lo) (size 57)) in
  let lo1 = vec_xor lo1 lo2 in
  let lo1 = vec_xor lo1 lo3 in
  let lo2 = vec_shift_right lo1 (size 64) in
  let lo3 = vec_shift_left lo1 (size 64) in
  let lo =  vec_xor lo lo3 in
  let lo' = lo2 in

  (* RIGHT SHIFT [x1:x0] BY 1,2,7 and xor with [x1:x0] *)
  let lo1 = cast U128 1 (vec_shift_right (cast U64 2 lo) (size 1)) in
  let lo2 = cast U128 1 (vec_shift_right (cast U64 2 lo) (size 2)) in
  let lo3 = cast U128 1 (vec_shift_right (cast U64 2 lo) (size 7)) in
  let lo1 = vec_xor lo1 lo2 in
  let lo1 = vec_xor lo1 lo3 in

  let lo1 = vec_xor lo1 lo' in
  let lo = vec_xor lo lo1 in

  let lo = vec_xor lo hi in
  lo


val gf128_clmul_wide_reduce_lemma: x:vec128 -> y:vec128 -> Lemma
  (let (hi, lo) = clmul_wide x y in
   to_elem (gf128_reduce hi lo) == GF.fmul_be #S.gf128 (to_elem x) (to_elem y))
let gf128_clmul_wide_reduce_lemma x y = admit()


val gf128_clmul_wide4_reduce_lemma:
    x1:vec128 -> x2:vec128 -> x3:vec128 -> x4:vec128
  -> y1:vec128 -> y2:vec128 -> y3:vec128 -> y4:vec128 -> Lemma
  (let (hi, lo) = clmul_wide4 x1 x2 x3 x4 y1 y2 y3 y4 in
   to_elem (gf128_reduce hi lo) == Vec.normalize4 (to_elem4 y1 y2 y3 y4) (to_elem4 x1 x2 x3 x4))
let gf128_clmul_wide4_reduce_lemma x1 x2 x3 x4 y1 y2 y3 y4 = admit()
