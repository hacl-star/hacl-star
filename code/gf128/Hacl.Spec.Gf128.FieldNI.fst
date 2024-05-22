module Hacl.Spec.Gf128.FieldNI

open FStar.Mul

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence

open Vale.Math.Poly2_s
open Vale.Math.Poly2
open Vale.Math.Poly2.Lemmas
open Vale.AES.GF128
open Vale.AES.GHash_BE
open Vale.Math.Poly2.Galois

open Hacl.Spec.GF128.Poly_s
open Hacl.Spec.GF128.PolyLemmas
open Hacl.Spec.GF128.PolyLemmas_helpers

module S = Spec.GF128
module GF = Spec.GaloisField
module Vec = Hacl.Spec.GF128.Vec
module B = Vale.Math.Poly2.Bits_s

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let to_elem (s:vec128) : S.elem =
  index (vec_v s) 0

inline_for_extraction noextract
let to_elem4 (x1:vec128) (x2:vec128) (x3:vec128) (x4:vec128) : Vec.elem4 =
  create4 (index (vec_v x1) 0) (index (vec_v x2) 0) (index (vec_v x3) 0) (index (vec_v x4) 0)

inline_for_extraction
let cl_add (x:vec128) (y:vec128) : Tot vec128 = vec_xor x y

val lemma_cl_add (x:vec128) (y:vec128) : Lemma
  (ensures cl_add x y == to_vec128 (add (of_vec128 x) (of_vec128 y)))

let lemma_cl_add x y =
  lemma_add_vec128 x y;
  ()

inline_for_extraction
let clmul_wide (x:vec128) (y:vec128) : Tot (vec128 & vec128) =
  let lo = vec_clmul_lo_lo x y in
  let m1 = vec_clmul_hi_lo x y in
  let m2 = vec_clmul_lo_hi x y in
  let hi = vec_clmul_hi_hi x y in
  let m1 = cl_add m1 m2 in
  let m2 = vec_shift_left m1 64ul in
  let m1 = vec_shift_right m1 64ul in
  let lo = cl_add lo m2 in
  let hi = cl_add hi m1 in
  (hi,lo)

val lemma_clmul_wide (x:vec128) (y:vec128) : Lemma
  (ensures (
    let (hi, lo) = clmul_wide x y in
    mul (of_vec128 x) (of_vec128 y) == add (shift (of_vec128 hi) 128) (of_vec128 lo) /\
    degree (of_vec128 hi) <= 126
  ))

let lemma_clmul_wide x y =
  (* vec128 variables *)
  let lo = vec_clmul_lo_lo x y in
  let m1 = vec_clmul_hi_lo x y in
  let m2 = vec_clmul_lo_hi x y in
  let hi = vec_clmul_hi_hi x y in
  let m12 = cl_add m1 m2 in
  let m12_0 = vec_shift_left m12 64ul in
  let m12_1 = vec_shift_right m12 64ul in
  let lo_m = cl_add lo m12_0 in
  let hi_m = cl_add hi m12_1 in
  (* poly variables *)
  let ab = of_vec128 x in
  let cd = of_vec128 y in
  let n = monomial 64 in
  let a = div ab n in
  let b = mod ab n in
  let c = div cd n in
  let d = mod cd n in
  let ac = mul a c in
  let ad = mul a d in
  let bc = mul b c in
  let bd = mul b d in
  (* vec128 lemmas *)
  vec_clmul_lo_lo_lemma x y;
  vec_clmul_hi_lo_lemma x y;
  vec_clmul_lo_hi_lemma x y;
  vec_clmul_hi_hi_lemma x y;
  lemma_cl_add m1 m2;
  lemma_vec128_double_shift (of_vec128 m12);
  lemma_cl_add lo m12_0;
  lemma_cl_add hi m12_1;
  (* poly lemmas *)
  lemma_shift_is_div ab 64;
  lemma_shift_is_div cd 64;
  lemma_div_distribute ad bc n;
  lemma_add_commute (div ad n) (div bc n);
  lemma_add_associate ac (div bc n) (div ad n);
  lemma_mod_distribute ad bc n;
  lemma_mul_commute (add (mod ad n) (mod bc n)) n;
  lemma_mul_distribute n (mod ad n) (mod bc n);
  lemma_mul_commute n (mod ad n);
  lemma_mul_commute n (mod bc n);
  lemma_add_commute (mul (mod ad n) n) (mul (mod bc n) n);
  lemma_add_commute bd (add (mul (mod bc n) n) (mul (mod ad n) n));
  assert (add (add ac (div bc n)) (div ad n) == of_vec128 hi_m); //OBSERVE
  assert (add (add (mul (mod bc n) n) (mul (mod ad n) n)) bd == of_vec128 lo_m); //OBSERVE
  lemma_split_define ab 64;
  lemma_split_define cd 64;
  lemma_gf128_mul a b c d 64;
  ()

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

  let m1 = vec_shift_left m 64ul in
  let m2 = vec_shift_right m 64ul in
  let lo = cl_add lo m1 in
  let hi = cl_add hi m2 in
  (hi, lo)

val lemma_clmul_wide4
  (x1:vec128) (x2:vec128) (x3:vec128) (x4:vec128)
  (y1:vec128) (y2:vec128) (y3:vec128) (y4:vec128) : Lemma
  (ensures (
    let (hi, lo) = clmul_wide4 x1 x2 x3 x4 y1 y2 y3 y4 in
    add (add (add
      (mul (of_vec128 x1) (of_vec128 y1))
      (mul (of_vec128 x2) (of_vec128 y2)))
      (mul (of_vec128 x3) (of_vec128 y3)))
      (mul (of_vec128 x4) (of_vec128 y4)) ==
    add (shift (of_vec128 hi) 128) (of_vec128 lo) /\
    degree (of_vec128 hi) <= 126
  ))

let lemma_clmul_wide4 x1 x2 x3 x4 y1 y2 y3 y4 =
  (* vec128 variables *)
  let lo1 = vec_clmul_lo_lo x1 y1 in
  let lo2 = vec_clmul_lo_lo x2 y2 in
  let lo3 = vec_clmul_lo_lo x3 y3 in
  let lo4 = vec_clmul_lo_lo x4 y4 in
  let lo_12 = cl_add lo1 lo2 in
  let lo_13 = cl_add lo_12 lo3 in
  let lo_14 = cl_add lo_13 lo4 in

  let m1 = vec_clmul_hi_lo x1 y1 in
  let m2 = vec_clmul_hi_lo x2 y2 in
  let m3 = vec_clmul_hi_lo x3 y3 in
  let m4 = vec_clmul_hi_lo x4 y4 in
  let m_12 = cl_add m1 m2 in
  let m_13 = cl_add m_12 m3 in
  let m_14 = cl_add m_13 m4 in

  let m1' = vec_clmul_lo_hi x1 y1 in
  let m2' = vec_clmul_lo_hi x2 y2 in
  let m3' = vec_clmul_lo_hi x3 y3 in
  let m4' = vec_clmul_lo_hi x4 y4 in
  let m' = cl_add m_14 m1' in
  let m_12' = cl_add m' m2' in
  let m_13' = cl_add m_12' m3' in
  let m_14' = cl_add m_13' m4' in

  let hi1 = vec_clmul_hi_hi x1 y1 in
  let hi2 = vec_clmul_hi_hi x2 y2 in
  let hi3 = vec_clmul_hi_hi x3 y3 in
  let hi4 = vec_clmul_hi_hi x4 y4 in
  let hi_12 = cl_add hi1 hi2 in
  let hi_13 = cl_add hi_12 hi3 in
  let hi_14 = cl_add hi_13 hi4 in

  let m_14_0 = vec_shift_left m_14' 64ul in
  let m_14_1 = vec_shift_right m_14' 64ul in
  let lo_m = cl_add lo_14 m_14_0 in
  let hi_m = cl_add hi_14 m_14_1 in
  (* poly variables *)
  let n = monomial 64 in
  let ab0 = of_vec128 x1 in
  let cd0 = of_vec128 y1 in
  let a0 = div ab0 n in
  let b0 = mod ab0 n in
  let c0 = div cd0 n in
  let d0 = mod cd0 n in
  let ac0 = mul a0 c0 in
  let ad0 = mul a0 d0 in
  let bc0 = mul b0 c0 in
  let bd0 = mul b0 d0 in

  let ab1 = of_vec128 x2 in
  let cd1 = of_vec128 y2 in
  let a1 = div ab1 n in
  let b1 = mod ab1 n in
  let c1 = div cd1 n in
  let d1 = mod cd1 n in
  let ac1 = mul a1 c1 in
  let ad1 = mul a1 d1 in
  let bc1 = mul b1 c1 in
  let bd1 = mul b1 d1 in

  let ab2 = of_vec128 x3 in
  let cd2 = of_vec128 y3 in
  let a2 = div ab2 n in
  let b2 = mod ab2 n in
  let c2 = div cd2 n in
  let d2 = mod cd2 n in
  let ac2 = mul a2 c2 in
  let ad2 = mul a2 d2 in
  let bc2 = mul b2 c2 in
  let bd2 = mul b2 d2 in

  let ab3 = of_vec128 x4 in
  let cd3 = of_vec128 y4 in
  let a3 = div ab3 n in
  let b3 = mod ab3 n in
  let c3 = div cd3 n in
  let d3 = mod cd3 n in
  let ac3 = mul a3 c3 in
  let ad3 = mul a3 d3 in
  let bc3 = mul b3 c3 in
  let bd3 = mul b3 d3 in
  (* vec128 lemmas *)
  vec_clmul_lo_lo_lemma x1 y1;
  vec_clmul_lo_lo_lemma x2 y2;
  vec_clmul_lo_lo_lemma x3 y3;
  vec_clmul_lo_lo_lemma x4 y4;
  vec_clmul_hi_lo_lemma x1 y1;
  vec_clmul_hi_lo_lemma x2 y2;
  vec_clmul_hi_lo_lemma x3 y3;
  vec_clmul_hi_lo_lemma x4 y4;
  vec_clmul_lo_hi_lemma x1 y1;
  vec_clmul_lo_hi_lemma x2 y2;
  vec_clmul_lo_hi_lemma x3 y3;
  vec_clmul_lo_hi_lemma x4 y4;
  vec_clmul_hi_hi_lemma x1 y1;
  vec_clmul_hi_hi_lemma x2 y2;
  vec_clmul_hi_hi_lemma x3 y3;
  vec_clmul_hi_hi_lemma x4 y4;
  lemma_cl_add lo1 lo2;
  lemma_cl_add lo_12 lo3;
  lemma_cl_add lo_13 lo4;
  lemma_cl_add m1 m2;
  lemma_cl_add m_12 m3;
  lemma_cl_add m_13 m4;
  lemma_cl_add m_14 m1';
  lemma_cl_add m' m2';
  lemma_cl_add m_12' m3';
  lemma_cl_add m_13' m4';
  lemma_cl_add hi1 hi2;
  lemma_cl_add hi_12 hi3;
  lemma_cl_add hi_13 hi4;
  lemma_vec128_double_shift (of_vec128 m_14');
  lemma_cl_add lo_14 m_14_0;
  lemma_cl_add hi_14 m_14_1;
  (* poly lemmas *)
  lemma_shift_is_div ab0 64;
  lemma_shift_is_div ab1 64;
  lemma_shift_is_div ab2 64;
  lemma_shift_is_div ab3 64;
  lemma_shift_is_div cd0 64;
  lemma_shift_is_div cd1 64;
  lemma_shift_is_div cd2 64;
  lemma_shift_is_div cd3 64;
  let bc_p = add (add (add bc0 bc1) bc2) bc3 in
  let ad_p  = add (add (add ad0 ad1) ad2) ad3 in
  let m_p  = add (add (add (add ad_p bc0) bc1) bc2) bc3 in
  let hi_p  = add (add (add ac0 ac1) ac2) ac3 in
  let lo_p  = add (add (add bd0 bd1) bd2) bd3 in
  lemma_add_commute lo_p (mul (mod m_p n) n);
  assert (add hi_p (div m_p n) == of_vec128 hi_m);
  assert (add (mul (mod m_p n) n) lo_p == of_vec128 lo_m);
  lemma_add_helper_m bc0 bc1 bc2 bc3 ad_p;
  assert (m_p == add bc_p ad_p);
  Vale.AES.GHash_BE.lemma_div_distribute bc_p ad_p n;
  lemma_add_associate (add (add (add ac0 ac1) ac2) ac3) (div bc_p n) (div ad_p n);
  lemma_mod_distribute bc_p ad_p n;
  lemma_mul_distribute_left (mod bc_p n) (mod ad_p n) n;
  lemma_split_define ab0 64;
  lemma_split_define ab1 64;
  lemma_split_define ab2 64;
  lemma_split_define ab3 64;
  lemma_split_define cd0 64;
  lemma_split_define cd1 64;
  lemma_split_define cd2 64;
  lemma_split_define cd3 64;
  lemma_gf128_mul_4 a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3;
  ()


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
  let lo1 = cast U128 1 (vec_shift_right (cast U64 2 lo) 63ul) in
  let lo2 = vec_shift_left lo1 64ul in
  let lo3 = cast U128 1 (vec_shift_left (cast U64 2 lo) 1ul) in
  let lo3 = vec_xor lo3 lo2 in

  let hi1 = cast U128 1 (vec_shift_right (cast U64 2 hi) 63ul) in
  let hi1 = vec_shift_left hi1 64ul in
  let hi2 = cast U128 1 (vec_shift_left (cast U64 2 hi) 1ul) in
  let hi2 = vec_xor hi2 hi1 in

  let lo1 = cast U128 1 (vec_shift_right (cast U64 2 lo) 63ul) in
  let lo1 = vec_shift_right lo1 64ul in
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
  let lo1 = cast U128 1 (vec_shift_left (cast U64 2 lo) 63ul) in
  let lo2 = cast U128 1 (vec_shift_left (cast U64 2 lo) 62ul) in
  let lo3 = cast U128 1 (vec_shift_left (cast U64 2 lo) 57ul) in
  let lo1 = vec_xor lo1 lo2 in
  let lo1 = vec_xor lo1 lo3 in
  let lo2 = vec_shift_right lo1 64ul in
  let lo3 = vec_shift_left lo1 64ul in
  let lo =  vec_xor lo lo3 in
  let lo' = lo2 in

  (* RIGHT SHIFT [x1:x0] BY 1,2,7 and xor with [x1:x0] *)
  let lo1 = cast U128 1 (vec_shift_right (cast U64 2 lo) 1ul) in
  let lo2 = cast U128 1 (vec_shift_right (cast U64 2 lo) 2ul) in
  let lo3 = cast U128 1 (vec_shift_right (cast U64 2 lo) 7ul) in
  let lo1 = vec_xor lo1 lo2 in
  let lo1 = vec_xor lo1 lo3 in

  let lo1 = vec_xor lo1 lo' in
  let lo = vec_xor lo lo1 in

  let lo = vec_xor lo hi in
  lo

val lemma_gf128_reduce (h:vec128) (l:vec128) : Lemma
  (requires degree (of_vec128 h) <= 126 /\ degree (of_vec128 l) <= 127)
  (ensures (
    let mm = monomial 128 in
    let g = add mm gf128_low in
    let a = shift (add (mul (of_vec128 h) mm) (of_vec128 l)) 1 in
    let x = reverse a 255 in
    gf128_reduce h l == to_vec128 (reverse (mod x g) 127)
  ))

let lemma_gf128_reduce h l =
  let n = monomial 64 in
  let nn = monomial 128 in
  let g = reverse gf128_low_shift 63 in
  let lo = of_vec128 l in
  let hi = of_vec128 h in
  let l0_r63 = shift (mod lo n) (-63) in
  let l1_r63 = shift (div lo n) (-63) in
  let l0_l1 = mod (shift (mod lo n) 1) n in
  let l1_l1 = mod (shift (div lo n) 1) n in
  let h0_r63 = shift (mod hi n) (-63) in
  let h1_r63 = shift (div hi n) (-63) in
  let h0_l1 = mod (shift (mod hi n) 1) n in
  let h1_l1 = mod (shift (div hi n) 1) n in

  lemma_vec128_shift_right_64 l 63ul;
  let lo1 = add (shift l1_r63 64) l0_r63 in
  lemma_vec128_double_shift lo1;
  lemma_shift_is_mul (mod lo1 n) 64;
  lemma_shift_left_cancel lo1 l0_r63 l1_r63;
  let lo2 = shift l0_r63 64 in
  lemma_vec128_shift_left_64 l 1ul;
  let lo3 = add (shift l1_l1 64) l0_l1 in
  lemma_cl_add (to_vec128 lo3) (to_vec128 lo2);
  lemma_add_left_shift l0_l1 l1_l1 l0_r63;
  let lo3 = add (shift (add l1_l1 l0_r63) 64) l0_l1 in

  lemma_vec128_shift_right_64 h 63ul;
  let hi1 = add (shift h1_r63 64) h0_r63 in
  lemma_vec128_double_shift hi1;
  lemma_shift_is_mul (mod hi1 n) 64;
  lemma_shift_left_cancel hi1 h0_r63 h1_r63;
  let hi1 = shift h0_r63 64 in
  lemma_vec128_shift_left_64 h 1ul;
  let hi2 = add (shift h1_l1 64) h0_l1 in
  lemma_cl_add (to_vec128 hi2) (to_vec128 hi1);
  lemma_add_left_shift h0_l1 h1_l1 h0_r63;
  let hi2 = add (shift (add h1_l1 h0_r63) 64) h0_l1 in

  lemma_shift_is_div lo1 64;
  lemma_shift_right_cancel lo1 l0_r63 l1_r63;
  let lo1 = l1_r63 in
  lemma_cl_add (to_vec128 hi2) (to_vec128 lo1);
  lemma_add_associate (shift (add h1_l1 h0_r63) 64) h0_l1 l1_r63;
  let hi2 = add (shift (add h1_l1 h0_r63) 64) (add h0_l1 l1_r63) in

  let lo = lo3 in
  let hi = hi2 in

  lemma_mul_x (of_vec128 h) (of_vec128 l);
  assert (shift (add (mul (of_vec128 h) nn) (of_vec128 l)) 1 == add (mul hi nn) lo); //OBSERVE

  let l0_l63 = mod (shift (mod lo n) 63) n in
  let l1_l63 = mod (shift (div lo n) 63) n in
  let l0_l62 = mod (shift (mod lo n) 62) n in
  let l1_l62 = mod (shift (div lo n) 62) n in
  let l0_l57 = mod (shift (mod lo n) 57) n in
  let l1_l57 = mod (shift (div lo n) 57) n in
  lemma_vec128_shift_left_64 (to_vec128 lo) 63ul;
  lemma_vec128_shift_left_64 (to_vec128 lo) 62ul;
  lemma_vec128_shift_left_64 (to_vec128 lo) 57ul;
  let lo1 = add (shift l1_l63 64) l0_l63 in
  let lo2 = add (shift l1_l62 64) l0_l62 in
  let lo3 = add (shift l1_l57 64) l0_l57 in
  lemma_cl_add (to_vec128 lo1) (to_vec128 lo2);
  lemma_add_left_shift_double l0_l63 l1_l63 l0_l62 l1_l62;
  let lo1 = add (shift (add l1_l63 l1_l62) 64) (add l0_l63 l0_l62) in
  lemma_cl_add (to_vec128 lo1) (to_vec128 lo3);
  lemma_add_left_shift_double (add l0_l63 l0_l62) (add l1_l63 l1_l62) l0_l57 l1_l57;
  lemma_mul_h_shift_right_mod (mod lo n) g;
  lemma_mul_h_shift_right_mod (div lo n) g;
  let lo1 = add (shift (mod (mul (div lo n) g) n) 64)
    (mod (mul (mod lo n) g) n) in
  lemma_vec128_double_shift lo1;
  lemma_shift_is_div lo1 64;
  lemma_shift_right_cancel lo1 (mod (mul (mod lo n) g) n)
    (mod (mul (div lo n) g) n);
  let lo2 = mod (mul (div lo n) g) n in
  lemma_shift_is_mul (mod lo1 n) 64;
  lemma_shift_left_cancel lo1 (mod (mul (mod lo n) g) n)
    (mod (mul (div lo n) g) n);
  let lo3 = shift (mod (mul (mod lo n) g) n) 64 in
  lemma_div_mod lo n;
  lemma_shift_is_mul (div lo n) 64;
  lemma_cl_add (to_vec128 lo) (to_vec128 lo3);
  lemma_add_left_shift (mod lo n) (div lo n) (mod (mul (mod lo n) g) n);

  let l_o = lo in
  let lo =  add (shift (add (div lo n) (mod (mul (mod lo n) g) n)) 64)
    (mod lo n) in
  let lo' = lo2 in

  let l0_r1 = shift (mod lo n) (-1) in
  let l1_r1 = shift (div lo n) (-1) in
  let l0_r2 = shift (mod lo n) (-2) in
  let l1_r2 = shift (div lo n) (-2) in
  let l0_r7 = shift (mod lo n) (-7) in
  let l1_r7 = shift (div lo n) (-7) in
  lemma_vec128_shift_right_64 (to_vec128 lo) 1ul;
  lemma_vec128_shift_right_64 (to_vec128 lo) 2ul;
  lemma_vec128_shift_right_64 (to_vec128 lo) 7ul;
  let lo1 = add (shift l1_r1 64) l0_r1 in
  let lo2 = add (shift l1_r2 64) l0_r2 in
  let lo3 = add (shift l1_r7 64) l0_r7 in
  lemma_cl_add (to_vec128 lo1) (to_vec128 lo2);
  lemma_add_left_shift_double l0_r1 l1_r1 l0_r2 l1_r2;
  let lo1 = add (shift (add l1_r1 l1_r2) 64) (add l0_r1 l0_r2) in
  lemma_cl_add (to_vec128 lo1) (to_vec128 lo3);
  lemma_add_left_shift_double (add l0_r1 l0_r2) (add l1_r1 l1_r2) l0_r7 l1_r7;
  lemma_mul_h_shift_left (mod lo n) g;
  lemma_mul_h_shift_left (div lo n) g;
  let lo1 = add (shift (div (mul (div lo n) g) n) 64)
    (div (mul (mod lo n) g) n) in
  
  lemma_cl_add (to_vec128 lo1) (to_vec128 lo');
  lemma_add_associate (shift (div (mul (div lo n) g) n) 64)
    (div (mul (mod lo n) g) n) (mod (mul (div l_o n) g) n);
  let lo1 = add (shift (div (mul (div lo n) g) n) 64)
    (add (div (mul (mod lo n) g) n) (mod (mul (div l_o n) g) n)) in
  lemma_div_mod lo n;
  lemma_shift_is_mul (div lo n) 64;
  lemma_cl_add (to_vec128 lo) (to_vec128 lo1);
  lemma_add_left_shift_double (mod lo n) (div lo n)
    (add (div (mul (mod lo n) g) n) (mod (mul (div l_o n) g) n))
    (div (mul (div lo n) g) n);
  lemma_shift_is_mul (add (div l_o n) (mod (mul (mod l_o n) g) n)) 64;
  lemma_div_mod_unique lo n (add (div l_o n) (mod (mul (mod l_o n) g) n)) (mod l_o n);
  let lo = add (shift (add (add (div l_o n) (mod (mul (mod l_o n) g) n))
    (div (mul (add (div l_o n) (mod (mul (mod l_o n) g) n)) g) n)) 64)
      (add (mod l_o n)
      (add (div (mul (mod l_o n) g) n) (mod (mul (div l_o n) g) n))) in

  lemma_reduce_helper l_o g;
  let y_10c = add (swap l_o 64) (mul (mask l_o 64) g) in
  assert (lo == add (swap y_10c 64) (mul (mask y_10c 64) g)); //OBSERVE

  lemma_add_commute (mul hi nn) l_o;
  lemma_shift_is_mul hi 128;
  lemma_cl_add (to_vec128 lo) (to_vec128 hi);

  lemma_gf128_degree ();
  lemma_reduce_rev_helper l_o hi gf128_low 64;
  let lo = add (add (swap y_10c 64) (mul (mask y_10c 64) g)) hi in
  let a = shift (add (mul (of_vec128 h) nn) (of_vec128 l)) 1 in
  let x = reverse a 255 in
  assert (lo == reverse (mod x (add nn gf128_low)) 127); //OBSERVE
  ()

let gf128_irred_elem_le = fun (i:nat) -> i = 127 || i = 126 || i = 125 || i = 120

let gf128_irred_elem_le_lemma (i:nat{i < 128}) : Lemma
  (UInt.nth #128 (v S.gf128_le.irred) i == gf128_irred_elem_le i) =
  assert_norm (UInt.nth #8 (v S.gf128_le.irred) 0 == true);
  assert_norm (UInt.nth #8 (v S.gf128_le.irred) 1 == false);
  assert_norm (UInt.nth #8 (v S.gf128_le.irred) 2 == false);
  assert_norm (UInt.nth #8 (v S.gf128_le.irred) 3 == false);
  assert_norm (UInt.nth #8 (v S.gf128_le.irred) 4 == false);
  assert_norm (UInt.nth #8 (v S.gf128_le.irred) 5 == true);
  assert_norm (UInt.nth #8 (v S.gf128_le.irred) 6 == true);
  assert_norm (UInt.nth #8 (v S.gf128_le.irred) 7 == true);

  assert_norm ((v S.gf128_le.irred) % pow2 8 == (v S.gf128_le.irred));
  UInt.slice_right_lemma #128 (UInt.to_vec (v S.gf128_le.irred)) 8;
  assert (UInt.from_vec #8 (Seq.slice (UInt.to_vec #128 (v S.gf128_le.irred)) 120 128) = (v S.gf128_le.irred) % pow2 8);
  assert (Seq.slice (UInt.to_vec #128 (v S.gf128_le.irred)) 120 128 = UInt.to_vec #8 (v S.gf128_le.irred));

  assert_norm ((v S.gf128_le.irred) / pow2 8 == 0);
  UInt.slice_left_lemma #128 (UInt.to_vec (v S.gf128_le.irred)) 120;
  assert (UInt.from_vec #120 (Seq.slice (UInt.to_vec #128 (v S.gf128_le.irred)) 0 120) = (v S.gf128_le.irred) / pow2 8);
  assert (Seq.slice (UInt.to_vec #128 (v S.gf128_le.irred)) 0 120 = UInt.to_vec #120 0);
  let aux_zero (n:nat{n < 120}) : Lemma (UInt.nth #128 (v S.gf128_le.irred) n == false) =
    UInt.zero_to_vec_lemma #120 n in

  Classical.forall_intro aux_zero;
  assert (UInt.nth #128 (v S.gf128_le.irred) i == gf128_irred_elem_le i)

let lemma_gf128_irred_le (_:unit) : Lemma
  (B.of_uint 128 (v S.gf128_le.irred) == gf128_low)
  =
  let aux (i:nat{i < 128}) : Lemma (UInt.nth #128 (v S.gf128_le.irred) i == gf128_irred_elem_le i) =
    gf128_irred_elem_le_lemma i in

  Classical.forall_intro aux;
  lemma_index_all ();
  lemma_reverse_define_all ();
  lemma_equal (of_seq (UInt.to_vec #128 (v S.gf128_le.irred))) (of_fun 128 gf128_irred_elem_le);
  lemma_equal (reverse (of_fun 128 gf128_irred_elem_le) 127) gf128_low

val gf128_clmul_wide_reduce_lemma: x:vec128 -> y:vec128 -> Lemma
  (let (hi, lo) = clmul_wide x y in
   to_elem (gf128_reduce hi lo) ==
    GF.reverse (GF.fmul #S.gf128_le (GF.reverse (to_elem x)) (GF.reverse (to_elem y))))
let gf128_clmul_wide_reduce_lemma x y =
  lemma_clmul_wide x y;
  let (hi, lo) = clmul_wide x y in
  assert (mul (of_vec128 x) (of_vec128 y) ==
    add (shift (of_vec128 hi) 128) (of_vec128 lo));
  lemma_gf128_reduce hi lo;
  lemma_shift_is_mul (of_vec128 hi) 128;
  let mm = monomial 128 in
  let g = add mm gf128_low in
  let a = shift (mul (of_vec128 x) (of_vec128 y)) 1 in
  let z = reverse a 255 in
  assert (gf128_reduce hi lo == to_vec128 (reverse (mod z g) 127));
  let x_r = reverse (of_vec128 x) 127 in
  let y_r = reverse (of_vec128 y) 127 in
  lemma_mul_reverse_shift_1 x_r y_r 127;
  assert (z == mul x_r y_r);
  lemma_gf128_irred_le ();
  assert (irred_poly S.gf128_le == g);
  assert (to_poly (GF.fmul (to_felem S.gf128_le x_r) (to_felem S.gf128_le y_r)) == mod z g);
  lemma_reverse S.gf128_le (GF.fmul (to_felem S.gf128_le x_r) (to_felem S.gf128_le y_r));
  assert (GF.reverse (GF.fmul (to_felem S.gf128_le x_r) (to_felem S.gf128_le y_r)) ==
    to_felem S.gf128_le (reverse (mod z g) 127));
  lemma_reverse S.gf128_le (to_elem x);
  lemma_reverse S.gf128_le (to_elem y)


val gf128_clmul_wide4_reduce_lemma:
    x1:vec128 -> x2:vec128 -> x3:vec128 -> x4:vec128
  -> y1:vec128 -> y2:vec128 -> y3:vec128 -> y4:vec128 -> Lemma
  (let (hi, lo) = clmul_wide4 x1 x2 x3 x4 y1 y2 y3 y4 in
   to_elem (gf128_reduce hi lo) == Vec.normalize4 (to_elem4 y1 y2 y3 y4) (to_elem4 x1 x2 x3 x4))
let gf128_clmul_wide4_reduce_lemma x1 x2 x3 x4 y1 y2 y3 y4 =
  lemma_clmul_wide4 x1 x2 x3 x4 y1 y2 y3 y4;
  let (hi, lo) = clmul_wide4 x1 x2 x3 x4 y1 y2 y3 y4 in
  assert (add (add (add
      (mul (of_vec128 x1) (of_vec128 y1))
      (mul (of_vec128 x2) (of_vec128 y2)))
      (mul (of_vec128 x3) (of_vec128 y3)))
      (mul (of_vec128 x4) (of_vec128 y4)) ==
    add (shift (of_vec128 hi) 128) (of_vec128 lo));
  lemma_gf128_reduce hi lo;
  lemma_shift_is_mul (of_vec128 hi) 128;
  let mm = monomial 128 in
  let g = add mm gf128_low in
  let a = shift (add (add (add
    (mul (of_vec128 x1) (of_vec128 y1))
    (mul (of_vec128 x2) (of_vec128 y2)))
    (mul (of_vec128 x3) (of_vec128 y3)))
    (mul (of_vec128 x4) (of_vec128 y4))) 1 in
  let z = reverse a 255 in
  assert (gf128_reduce hi lo == to_vec128 (reverse (mod z g) 127));
  lemma_mul_reduce_helper1 (of_vec128 x1) (of_vec128 x2) (of_vec128 x3)
    (of_vec128 x4) (of_vec128 y1) (of_vec128 y2) (of_vec128 y3) (of_vec128 y4);
  let x1_r = reverse (of_vec128 x1) 127 in
  let x2_r = reverse (of_vec128 x2) 127 in
  let x3_r = reverse (of_vec128 x3) 127 in
  let x4_r = reverse (of_vec128 x4) 127 in
  let y1_r = reverse (of_vec128 y1) 127 in
  let y2_r = reverse (of_vec128 y2) 127 in
  let y3_r = reverse (of_vec128 y3) 127 in
  let y4_r = reverse (of_vec128 y4) 127 in
  assert (z == add (add (add (mul x1_r y1_r) (mul x2_r y2_r))
    (mul x3_r y3_r)) (mul x4_r y4_r));
  lemma_gf128_irred_le ();
  assert (irred_poly S.gf128_le == g);
  lemma_mul_reduce_helper2 (mul x1_r y1_r) (mul x2_r y2_r)
    (mul x3_r y3_r) (mul x4_r y4_r) g;
  assert (reverse (mod z g) 127 == add (add (add (reverse (mod (mul x1_r y1_r) g) 127)
    (reverse (mod (mul x2_r y2_r) g) 127)) (reverse (mod (mul x3_r y3_r) g) 127))
    (reverse (mod (mul x4_r y4_r) g) 127));
  assert (reverse (mod z g) 127 == to_poly (GF.fadd (GF.fadd (GF.fadd
    (GF.reverse (GF.fmul (to_felem S.gf128_le x1_r) (to_felem S.gf128_le y1_r)))
    (GF.reverse (GF.fmul (to_felem S.gf128_le x2_r) (to_felem S.gf128_le y2_r))))
    (GF.reverse (GF.fmul (to_felem S.gf128_le x3_r) (to_felem S.gf128_le y3_r))))
    (GF.reverse (GF.fmul (to_felem S.gf128_le x4_r) (to_felem S.gf128_le y4_r)))));
  lemma_reverse S.gf128_le (to_elem x1);
  lemma_reverse S.gf128_le (to_elem x2);
  lemma_reverse S.gf128_le (to_elem x3);
  lemma_reverse S.gf128_le (to_elem x4);
  lemma_reverse S.gf128_le (to_elem y1);
  lemma_reverse S.gf128_le (to_elem y2);
  lemma_reverse S.gf128_le (to_elem y3);
  lemma_reverse S.gf128_le (to_elem y4)
