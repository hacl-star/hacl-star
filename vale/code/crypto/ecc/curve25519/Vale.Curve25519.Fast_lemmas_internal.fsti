module Vale.Curve25519.Fast_lemmas_internal

open Vale.Def.Words_s
open Vale.Def.Types_s
open FStar.Mul

val lemma_mul_bounds_le (x b_x y b_y:nat) : Lemma
  (requires x <= b_x /\ y <= b_y)
  (ensures x * y <= b_x * b_y)

val lemma_mul_pow2_bound (b:nat{b > 1}) (x y:natN (pow2 b)) :
  Lemma (x * y < pow2 (2*b) - 1 /\
         x * y <= pow2 (2*b) - 2*pow2(b) + 1)

val lemma_mul_bound64 (x y:nat64) :
  Lemma (x * y < pow2_128 - 1 /\ x * y <= pow2_128 - 2*pow2_64 + 1)

(* Intel manual mentions this fact *)
val lemma_intel_prod_sum_bound (w x y z:nat64) : Lemma
    (requires true)
    (ensures w * x + y + z < pow2_128)

val lemma_double_bound (x:nat64) :
  Lemma (add_wrap x x < pow2_64 - 1)


