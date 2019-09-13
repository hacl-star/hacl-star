module Vale.Curve25519.FastMul_helpers

open Vale.Def.Words_s
open Vale.Def.Types_s
open FStar.Mul
open FStar.Tactics
open FStar.Tactics.CanonCommSemiring
open Vale.Curve25519.Fast_defs


let int_canon = fun _ -> norm [delta]; int_semiring () //; dump "Final"

val lemma_partial_sum (
      a0 a1 a2 a3 a4
      b0 b1 b2 b3 b4
      s1 s2 s3 s4 s5 c:nat64) : Lemma
  (requires(let s1', c1 = add_carry a1 b0 0 in
            let s2', c2 = add_carry a2 b1 c1 in
            let s3', c3 = add_carry a3 b2 c2 in
            let s4', c4 = add_carry a4 b3 c3 in
            let s5', c5 = add_carry 0 b4 c4 in
            s1 == s1' /\
            s2 == s2' /\
            s3 == s3' /\
            s4 == s4' /\
            s5 == s5' /\
            c == c5))
  (ensures pow2_six a0 (a1 + b0) (a2 + b1) (a3 + b2) (a4 + b3) b4 =
           pow2_seven a0 s1 s2 s3 s4 s5 c)

val lemma_partial_sum_a2b (
      a0 a1 a2 a3 a4 a5
      b0 b1 b2 b3 b4
      s1 s2 s3 s4 s5:nat64) : Lemma
  (requires(let s1', c1 = add_carry a2 b0 0 in
            let s2', c2 = add_carry a3 b1 c1 in
            let s3', c3 = add_carry a4 b2 c2 in
            let s4', c4 = add_carry a5 b3 c3 in
            let s5', c5 = add_carry 0 b4 c4 in
            s1 == s1' /\
            s2 == s2' /\
            s3 == s3' /\
            s4 == s4' /\
            s5 == s5' /\
            0 == c5))
  (ensures pow2_seven a0 a1 (a2 + b0) (a3 + b1) (a4 + b2) (a5 + b3) b4 =
           pow2_seven a0 a1 s1 s2 s3 s4 s5)

val lemma_partial_sum_a3b (
      a0 a1 a2 a3 a4 a5 a6
      b0 b1 b2 b3 b4
      s1 s2 s3 s4 s5:nat64) : Lemma
  (requires(let s1', c1 = add_carry a3 b0 0 in
            let s2', c2 = add_carry a4 b1 c1 in
            let s3', c3 = add_carry a5 b2 c2 in
            let s4', c4 = add_carry a6 b3 c3 in
            let s5', c5 = add_carry 0 b4 c4 in
            s1 == s1' /\
            s2 == s2' /\
            s3 == s3' /\
            s4 == s4' /\
            s5 == s5' /\
            0 == c5))
  (ensures pow2_eight a0 a1 a2 (a3 + b0) (a4 + b1) (a5 + b2) (a6 + b3) b4 =
           pow2_eight a0 a1 a2 s1 s2 s3 s4 s5)

val lemma_sum_a1b
      (a0 a1:nat64)
      (a0b:nat) (a0b_0 a0b_1 a0b_2 a0b_3 a0b_4:nat64)
      (a1b:nat) (a1b_0 a1b_1 a1b_2 a1b_3 a1b_4:nat64)
      (b:nat)   (b0 b1 b2 b3:nat64)
      (s1 s2 s3 s4 s5
      c:nat64) : Lemma
  (requires a0b = pow2_five a0b_0 a0b_1 a0b_2 a0b_3 a0b_4 /\
            a1b = pow2_five a1b_0 a1b_1 a1b_2 a1b_3 a1b_4 /\
            b = pow2_four b0 b1 b2 b3 /\
            a0b = mul_nats a0 b /\
            a1b = mul_nats a1 b /\
           (let s1', c1 = add_carry a0b_1 a1b_0 0 in
            let s2', c2 = add_carry a0b_2 a1b_1 c1 in
            let s3', c3 = add_carry a0b_3 a1b_2 c2 in
            let s4', c4 = add_carry a0b_4 a1b_3 c3 in
            let s5', c5 = add_carry 0 a1b_4 c4 in
            s1 == s1' /\
            s2 == s2' /\
            s3 == s3' /\
            s4 == s4' /\
            s5 == s5' /\
            c5 == c))
  (ensures (pow2_two a0 a1) * b ==
           pow2_seven a0b_0 s1 s2 s3 s4 s5 c)

val lemma_sum_a2b
      (a0 a1 a2:nat64)
      (a0a1b:nat) (a0a1b_0 a0a1b_1 a0a1b_2 a0a1b_3 a0a1b_4 a0a1b_5:nat64)
      (a2b:nat) (a2b_0 a2b_1 a2b_2 a2b_3 a2b_4:nat64)
      (b:nat)   (b0 b1 b2 b3:nat64)
      (s1 s2 s3 s4 s5:nat64) : Lemma
  (requires a0a1b = pow2_six a0a1b_0 a0a1b_1 a0a1b_2 a0a1b_3 a0a1b_4 a0a1b_5  /\
            a2b = pow2_five a2b_0 a2b_1 a2b_2 a2b_3 a2b_4 /\
            b = pow2_four b0 b1 b2 b3 /\
            a0a1b = mul_nats (pow2_two a0 a1) b /\
            a2b = mul_nats a2 b /\
           (let s1', c1 = add_carry a0a1b_2 a2b_0 0 in
            let s2', c2 = add_carry a0a1b_3 a2b_1 c1 in
            let s3', c3 = add_carry a0a1b_4 a2b_2 c2 in
            let s4', c4 = add_carry a0a1b_5 a2b_3 c3 in
            let s5', c5 = add_carry 0 a2b_4 c4 in
            s1 == s1' /\
            s2 == s2' /\
            s3 == s3' /\
            s4 == s4' /\
            s5 == s5' /\
            c5 == 0))
  (ensures (pow2_three a0 a1 a2) * b ==
           pow2_seven a0a1b_0 a0a1b_1 s1 s2 s3 s4 s5)

val lemma_sum_a3b
      (a0 a1 a2 a3:nat64)
      (a0a1a2b:nat) (a0a1a2b_0 a0a1a2b_1 a0a1a2b_2 a0a1a2b_3 a0a1a2b_4 a0a1a2b_5 a0a1a2b_6:nat64)
      (a3b:nat) (a3b_0 a3b_1 a3b_2 a3b_3 a3b_4:nat64)
      (b:nat)   (b0 b1 b2 b3:nat64)
      (s1 s2 s3 s4 s5:nat64) : Lemma
  (requires a0a1a2b = pow2_seven a0a1a2b_0 a0a1a2b_1 a0a1a2b_2 a0a1a2b_3 a0a1a2b_4 a0a1a2b_5 a0a1a2b_6 /\
            a3b = pow2_five a3b_0 a3b_1 a3b_2 a3b_3 a3b_4 /\
            b = pow2_four b0 b1 b2 b3 /\
            a0a1a2b = mul_nats (pow2_three a0 a1 a2) b /\
            a3b = mul_nats a3 b /\
           (let s1', c1 = add_carry a0a1a2b_3 a3b_0 0 in
            let s2', c2 = add_carry a0a1a2b_4 a3b_1 c1 in
            let s3', c3 = add_carry a0a1a2b_5 a3b_2 c2 in
            let s4', c4 = add_carry a0a1a2b_6 a3b_3 c3 in
            let s5', c5 = add_carry 0 a3b_4 c4 in
            s1 == s1' /\
            s2 == s2' /\
            s3 == s3' /\
            s4 == s4' /\
            s5 == s5' /\
            c5 == 0))
  (ensures (pow2_four a0 a1 a2 a3) * b ==
           pow2_eight a0a1a2b_0 a0a1a2b_1 a0a1a2b_2 s1 s2 s3 s4 s5)
