module Vale.Curve25519.FastHybrid_helpers

open Vale.Def.Words_s
open Vale.Def.Types_s
open FStar.Mul
open FStar.Tactics
open FStar.Tactics.CanonCommSemiring
open Vale.Curve25519.Fast_defs
open FStar.Calc

let int_canon = fun _ -> norm [delta]; int_semiring () //; dump "Final"

unfold let pow2_63:nat = 0x8000000000000000

let _ = assert_norm (pow2_63 == pow2 63)

let lemma_mul_pow256_add (x y:nat) :
  Lemma ((x + y * pow2_256) % prime == (x + y * 38) % prime)
  =
  assert_norm (pow2_256 % prime == 38);
  ()


val lemma_carry_prime (a0 a1 a2 a3 a0' a1' a2' a3' carry_in:nat64) (carry:bit) : Lemma
  (requires pow2_five a0' a1' a2' a3' carry == pow2_four a0 a1 a2 a3 + carry_in * 38 /\
            carry_in * 38 - 1 + 38 < pow2_64)
  (ensures a0' + carry * 38 < pow2_64 /\
           (pow2_four (a0' + carry * 38) a1' a2' a3') % prime == (pow2_four a0 a1 a2 a3 + carry_in * pow2_256) % prime)

val lemma_fast_mul1 (a:nat)
               (b a0 a1 a2 a3
                ba0_hi ba0_lo
                ba1_hi ba1_lo
                ba2_hi ba2_lo
                ba3_hi ba3_lo
                s1 s2 s3 s4:nat64) : Lemma
  (requires a = pow2_four a0 a1 a2 a3 /\

            pow2_64 * ba0_hi + ba0_lo == b * a0 /\
            pow2_64 * ba1_hi + ba1_lo == b * a1 /\
            pow2_64 * ba2_hi + ba2_lo == b * a2 /\
            pow2_64 * ba3_hi + ba3_lo == b * a3 /\

           (let s1', c1 = add_carry ba1_lo ba0_hi 0 in
            let s2', c2 = add_carry ba2_lo ba1_hi c1 in
            let s3', c3 = add_carry ba3_lo ba2_hi c2 in
            let s4', c4 = add_carry ba3_hi 0 c3 in
            s1 == s1' /\
            s2 == s2' /\
            s3 == s3' /\
            s4 == s4' /\
            c4 == 0)
  )
  (ensures pow2_five ba0_lo s1 s2 s3 s4 == a * b)

val lemma_addition (a d:nat) (a0 a1 a2 a3 d0 d1 d2 d3 d4:nat64)
                   (s0 s1 s2 s3 s4:nat64) : Lemma
  (requires a = pow2_four a0 a1 a2 a3 /\
            d = pow2_five d0 d1 d2 d3 d4 /\
           (let s0', c0 = add_carry a0 d0 0 in
            let s1', c1 = add_carry a1 d1 c0 in
            let s2', c2 = add_carry a2 d2 c1 in
            let s3', c3 = add_carry a3 d3 c2 in
            let s4', c4 = add_carry d4  0 c3 in
            s0 == s0' /\
            s1 == s1' /\
            s2 == s2' /\
            s3 == s3' /\
            s4 == s4' /\
            c4 == 0))
  (ensures a + d == pow2_five s0 s1 s2 s3 s4)

val lemma_carry_wide (a0 a1 a2 a3 a4 a5 a6 a7
                      d0 d1 d2 d3 carry
                      d0' d1' d2' d3':nat64) : Lemma
  (requires pow2_five d0 d1 d2 d3 carry == 38 * pow2_four a4 a5 a6 a7 + pow2_four a0 a1 a2 a3 /\
            pow2_four d0' d1' d2' d3' % prime == ((pow2_four d0 d1 d2 d3) + carry * pow2_256) % prime)
  (ensures (pow2_four d0' d1' d2' d3') % prime == (pow2_eight a0 a1 a2 a3 a4 a5 a6 a7) % prime)

val lemma_carry_sub_prime (a0 a1 a2 a3 a0' a1' a2' a3' carry_in:nat64) (carry:bit) : Lemma
  (requires pow2_four a0' a1' a2' a3' - carry * pow2_256 == pow2_four a0 a1 a2 a3 - carry_in * 38 /\
            carry_in * 38 - 1 + 38 < pow2_64)
  (ensures a0' - carry * 38 >= 0 /\
           (pow2_four (a0' - carry * 38) a1' a2' a3') % prime == (pow2_four a0 a1 a2 a3 - carry_in * pow2_256) % prime)

val lemma_fmul (a0 a1 a2 a3 b d0 d1 d2 d3 carry:nat64) : Lemma
  (requires pow2_five d0 d1 d2 d3 carry == (pow2_four a0 a1 a2 a3) * b /\
            b < 131072)
  (ensures carry * 38 < pow2_63)
