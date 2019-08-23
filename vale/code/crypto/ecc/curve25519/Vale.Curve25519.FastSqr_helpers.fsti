module Vale.Curve25519.FastSqr_helpers

open Vale.Def.Words_s
open Vale.Def.Types_s
open FStar.Mul
open FStar.Tactics
open FStar.Tactics.CanonCommSemiring

open Vale.Curve25519.Fast_defs

open FStar.Math.Lemmas

let int_canon = fun _ -> norm [delta]; int_semiring () //; dump "Final"

val lemma_sqr_part3
      (a:nat) (a0 a1 a2 a3:nat64)
      (a0_sqr_hi a0_sqr_lo
       a1_sqr_hi a1_sqr_lo
       a2_sqr_hi a2_sqr_lo
       a3_sqr_hi a3_sqr_lo:nat64)
       (r8 r9 r10 r11 r12 r13 r14:nat64)
       (d0 d1 d2 d3 d4 d5 d6 d7:nat64) (c:bit) : Lemma
  (requires a = pow2_four a0 a1 a2 a3 /\
            pow2_64 * a0_sqr_hi + a0_sqr_lo == a0 * a0 /\
            pow2_64 * a1_sqr_hi + a1_sqr_lo == a1 * a1 /\
            pow2_64 * a2_sqr_hi + a2_sqr_lo == a2 * a2 /\
            pow2_64 * a3_sqr_hi + a3_sqr_lo == a3 * a3 /\
           (let s1, c1 = add_carry r8  a0_sqr_hi 0 in
            let s2, c2 = add_carry r9  a1_sqr_lo c1 in
            let s3, c3 = add_carry r10 a1_sqr_hi c2 in
            let s4, c4 = add_carry r11 a2_sqr_lo c3 in
            let s5, c5 = add_carry r12 a2_sqr_hi c4 in
            let s6, c6 = add_carry r13 a3_sqr_lo c5 in
            let s7, c7 = add_carry r14 a3_sqr_hi c6 in
            d0 == a0_sqr_lo /\
            d1 == s1 /\
            d2 == s2 /\
            d3 == s3 /\
            d4 == s4 /\
            d5 == s5 /\
            d6 == s6 /\
            d7 == s7 /\
            c  == c7))
  (ensures pow2_nine d0 d1 d2 d3 d4 d5 d6 d7 c ==
           pow2_eight (mul_nats a0 a0) r8 ((mul_nats a1 a1) + r9) r10 ((mul_nats a2 a2) + r11) r12 ((mul_nats a3 a3) + r13) r14)


val lemma_sqr (a:int) (a0 a1 a2 a3
               r8 r9 r10 r11 r12 r13 rax rcx
               r8' r9' r10' r11' r12' r13' r14'
               d0 d1 d2 d3 d4 d5 d6 d7:nat64) (cf:bit) : Lemma
  (requires a = pow2_four a0 a1 a2 a3 /\

            a*a == pow2_seven (mul_nats a0 a0) (2*(mul_nats a0 a1)) (2*(mul_nats a0 a2) + (mul_nats a1 a1))
                              (2*((mul_nats a0 a3) + (mul_nats a1 a2))) (2*(mul_nats a1 a3) + (mul_nats a2 a2)) (2*(mul_nats a2 a3)) (mul_nats a3 a3) /\

            pow2_six r8 r9 r10 r11 r12 r13 ==
            pow2_five (mul_nats a0 a1) (mul_nats a0 a2) (mul_nats a0 a3) (mul_nats a1 a3) (mul_nats a2 a3) /\
            pow2_64 * rcx + rax == a1 * a2 /\

            pow2_seven r8' r9' r10' r11' r12' r13' r14' ==
            pow2_six (2*r8) (2*r9) (2*(r10+rax)) (2*(r11+rcx)) (2*r12) (2*r13) /\

            pow2_nine d0 d1 d2 d3 d4 d5 d6 d7 cf ==
            pow2_eight (mul_nats a0 a0) r8' ((mul_nats a1 a1) + r9') r10' ((mul_nats a2 a2) + r11') r12' ((mul_nats a3 a3) + r13') r14')
  (ensures  a*a == pow2_eight d0 d1 d2 d3 d4 d5 d6 d7)

