module Hacl.Spec.GF128.Poly_s

open FStar.UInt

open Lib.IntTypes
open Lib.IntVector

open Vale.Math.Poly2_s
open Vale.Math.Poly2.Bits_s
open Vale.Math.Poly2

inline_for_extraction noextract
let vec128 = vec_t U128 1

inline_for_extraction noextract
let uint_to_vec128 (s:UInt.uint_t 128) : vec128 =
  vec_t_v (Lib.Sequence.create 1 (mk_int s))

inline_for_extraction noextract
let vec128_to_uint (s:vec128) : UInt.uint_t 128 =
  v (Lib.Sequence.index (vec_v s) 0)

inline_for_extraction noextract
let to_vec128 (a:poly{degree a < 128}) : vec128 =
  uint_to_vec128 (to_uint 128 a)

inline_for_extraction noextract
let of_vec128 (u:vec128) : a:poly{degree a < 128} =
  reveal_defs ();
  of_uint 128 (vec128_to_uint u)

assume val vec_clmul_lo_lo_lemma: x:vec128 -> y:vec128 -> Lemma
  (of_vec128 (vec_clmul_lo_lo x y) ==
    mul (mod (of_vec128 x) (monomial 64)) (mod (of_vec128 y) (monomial 64)))

assume val vec_clmul_hi_lo_lemma: x:vec128 -> y:vec128 -> Lemma
  (of_vec128 (vec_clmul_hi_lo x y) ==
    mul (shift (of_vec128 x) (-64)) (mod (of_vec128 y) (monomial 64)))

assume val vec_clmul_lo_hi_lemma: x:vec128 -> y:vec128 -> Lemma
  (of_vec128 (vec_clmul_lo_hi x y) ==
    mul (mod (of_vec128 x) (monomial 64)) (shift (of_vec128 y) (-64)))

assume val vec_clmul_hi_hi_lemma: x:vec128 -> y:vec128 -> Lemma
  (of_vec128 (vec_clmul_hi_hi x y) ==
    mul (shift (of_vec128 x) (-64)) (shift (of_vec128 y) (-64)))
