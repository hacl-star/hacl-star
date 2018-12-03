module Fast_lemmas_external

open Words_s
open Types_s
open FStar.Mul
open Fast_defs

val lemma_overflow (dst_hi dst_lo addend:nat64) (old_overflow:bit) : Lemma
  (requires dst_hi < pow2_64 - 1 /\
            (dst_hi < pow2_64 - 2 \/ dst_lo <= 1) /\
            addend < pow2_64 - 1 /\
            (old_overflow = 0 \/ addend < pow2_64 - 2))
  (ensures dst_hi < pow2_64 - 2 \/ dst_lo + addend + old_overflow < pow2_64)

val lemma_prod_bounds (dst_hi dst_lo x y:nat64) : Lemma
  (requires pow2_64 * dst_hi + dst_lo == x * y)
  (ensures  dst_hi < pow2_64 - 1 /\
            (dst_hi < pow2_64 - 2 \/ dst_lo <= 1)
  )
