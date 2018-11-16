module Fast_lemmas

open Words_s
open Types_s
open FStar.Mul
open FStar.Math.Lemmas

let lemma_mul_bounds_le (x b_x y b_y:nat) : Lemma 
  (requires x <= b_x /\ y <= b_y)
  (ensures x * y <= b_x * b_y)
  =
  lemma_mult_le_right b_x y b_y;
  lemma_mult_le_right y x b_x;
  ()

let lemma_mul_pow2_bound (b:nat{b > 1}) (x y:natN (pow2 b)) :
  Lemma (x * y < pow2 (2*b) - 1 /\
         x * y <= pow2 (2*b) - 2*pow2(b) + 1)
  =
  lemma_mul_bounds_le x (pow2 b - 1) y (pow2 b -1);
  pow2_plus b b;
  assert ( (pow2 b - 1) * (pow2 b -1) = pow2 (2*b) - 2*pow2(b) + 1);
  ()

let lemma_mul_bound64 (x y:nat64) :
  Lemma (x * y < pow2_128 - 1 /\ x * y <= pow2_128 - 2*pow2_64 + 1)
 = 
 assert_norm (pow2 64 == pow2_64);
 assert_norm (pow2 128 == pow2_128);
 lemma_mul_pow2_bound 64 x y;
 ()

(* Intel manual mentions this fact *)
let lemma_intel_prod_sum_bound (w x y z:nat64) : Lemma
    (requires true)
    (ensures w * x + y + z < pow2_128)
    =
    lemma_mul_bound64 w x;
    ()

let lemma_prod_bounds (dst_hi dst_lo x y:nat64) : Lemma
  (requires pow2_64 * dst_hi + dst_lo == x * y)
  (ensures  dst_hi < pow2_64 - 1 /\
            (dst_hi < pow2_64 - 2 \/ dst_lo <= 1)
  )
  =
  let result = x * y in
  lemma_div_mod result pow2_64;
  //assert (result = pow2_64 * (result / pow2_64) + result % pow2_64);
  //assert (result % pow2_64 == dst_lo);
  //assert (result / pow2_64 == dst_hi);
  lemma_mul_bound64 x y;
  ()

let lemma_double_bound (x:nat64) : 
  Lemma (add_wrap x x < pow2_64 - 1)
  =
  ()

