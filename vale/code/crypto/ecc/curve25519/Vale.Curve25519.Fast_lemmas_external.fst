module Vale.Curve25519.Fast_lemmas_external

open Vale.Def.Words_s
open Vale.Def.Types_s
open FStar.Mul
open Vale.Curve25519.Fast_lemmas_internal

let lemma_overflow (dst_hi dst_lo addend:nat64) (old_overflow:bit) : Lemma
  (requires dst_hi < pow2_64 - 1 /\
            (dst_hi < pow2_64 - 2 \/ dst_lo <= 1) /\
            addend < pow2_64 - 1 /\
            (old_overflow = 0 \/ addend < pow2_64 - 2))
  (ensures dst_hi < pow2_64 - 2 \/ dst_lo + addend + old_overflow < pow2_64)
  =
  ()


let lemma_prod_bounds (dst_hi dst_lo x y:nat64) : Lemma
  (requires pow2_64 * dst_hi + dst_lo == x * y)
  (ensures  dst_hi < pow2_64 - 1 /\
            (dst_hi < pow2_64 - 2 \/ dst_lo <= 1)
  )
  =
  let result = x * y in
  FStar.Math.Lemmas.lemma_div_mod result pow2_64;
  //assert (result = pow2_64 * (result / pow2_64) + result % pow2_64);
  //assert (result % pow2_64 == dst_lo);
  //assert (result / pow2_64 == dst_hi);
  lemma_mul_bound64 x y;
  ()
