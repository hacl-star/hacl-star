module FastUtil_helpers

open Words_s
open Types_s
open FStar.Mul
open FStar.Tactics
open CanonCommSemiring
open Fast_defs
open Fast_lemmas

let int_canon = fun _ -> canon_semiring int_cr //; dump "Final"

let sub_carry (x y:nat64) (c:bit) : nat64 & (c':bit)
  =
  (x - (y + c)) % pow2_64,
  (if x - (y + c) < 0 then 1 else 0)

#push-options "--z3rlimit 3000 --max_fuel 0 --max_ifuel 0"
// Passes
(*
let lemma_sub2
      (a:nat) (a0 a1:nat64)      
      (b:nat) (b0 b1:nat64)
      (s1 s2:nat64) (c:bit) : Lemma
  (requires a = pow2_two a0 a1 /\
            b = pow2_two b0 b1 /\            
           (let s1', c1 = sub_carry a0 b0 0 in
            let s2', c2 = sub_carry a1 b1 c1 in
            s1 == s1' /\
            s2 == s2' /\
            c  == c2))
  (ensures a - b == pow2_two s1 s2 - c * pow2_128)
  =
  ()
*)
// Passes
let lemma_sub3
      (a:nat) (a0 a1 a2:nat64)      
      (b:nat) (b0 b1 b2:nat64)
      (s1 s2 s3:nat64) (c:bit) : Lemma
  (requires a = pow2_three a0 a1 a2 /\
            b = pow2_three b0 b1 b2 /\            
           (let s1', c1 = sub_carry a0 b0 0 in
            let s2', c2 = sub_carry a1 b1 c1 in
            let s3', c3 = sub_carry a2 b2 c2 in
            s1 == s1' /\
            s2 == s2' /\
            s3 == s3' /\
            c  == c3))
  (ensures a - b == pow2_three s1 s2 s3 - c * pow2_192)
  =
  ()
#pop-options

// Unclear why lemma_sub2 and lemma_sub3 pass, but lemma_sub4 fails without explicit help

let pow2int_three (c0 c1 c2:int) : int = c0 + c1 * pow2_64 + c2 * pow2_128
let pow2int_four (c0 c1 c2 c3:int) : int = c0 + c1 * pow2_64 + c2 * pow2_128 + c3 * pow2_192

let lemma_pow2_int_34 (c0 c1 c2 c3:int) : 
  Lemma (pow2int_four c0 c1 c2 c3 == pow2int_three c0 c1 c2 + c3 * pow2_192)
  =
  ()

#push-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0"
let lemma_sub
      (a:nat) (a0 a1 a2 a3:nat64)      
      (b:nat) (b0 b1 b2 b3:nat64)
      (s1 s2 s3 s4:nat64) (c:bit) : Lemma
  (requires a = pow2_four a0 a1 a2 a3 /\
            b = pow2_four b0 b1 b2 b3 /\            
           (let s1', c1 = sub_carry a0 b0 0 in
            let s2', c2 = sub_carry a1 b1 c1 in
            let s3', c3 = sub_carry a2 b2 c2 in
            let s4', c4 = sub_carry a3 b3 c3 in
            s1 == s1' /\
            s2 == s2' /\
            s3 == s3' /\
            s4 == s4' /\
            c  == c4))
  (ensures a - b == pow2_four s1 s2 s3 s4 - c * pow2_256)
  =
  let a_minus_b = a - b in
  assert_by_tactic (a_minus_b == pow2int_four (a0 - b0) (a1 - b1) (a2 - b2) (a3 - b3)) int_canon;
  let a_three = pow2_three a0 a1 a2 in
  let b_three = pow2_three b0 b1 b2 in
  let a3_minus_b3 = a_three - b_three in
  assert_by_tactic (a3_minus_b3 == pow2int_three (a0 - b0) (a1 - b1) (a2 - b2)) int_canon;
  lemma_pow2_int_34 (a0 - b0) (a1 - b1) (a2 - b2) (a3 - b3);
  assert (pow2int_four (a0 - b0) (a1 - b1) (a2 - b2) (a3 - b3) == pow2int_three (a0 - b0) (a1 - b1) (a2 - b2) + (a3 - b3) * pow2_192); 
  assert (a_minus_b == a3_minus_b3 + (a3 - b3) * pow2_192);
  let s1', c1 = sub_carry a0 b0 0 in
  let s2', c2 = sub_carry a1 b1 c1 in
  let s3', c3 = sub_carry a2 b2 c2 in
  let s4', c4 = sub_carry a3 b3 c3 in
  lemma_sub3 a_three a0 a1 a2
             b_three b0 b1 b2
             s1 s2 s3 c3;
  assert (a3_minus_b3 = pow2_three s1 s2 s3 - c3 * pow2_192);     
  assert (a_minus_b == pow2_three s1 s2 s3 + (a3 - b3 - c3) * pow2_192);
  assert_by_tactic ((a3 - b3 - c3) * pow2_192 == s4 * pow2_192 - c * pow2_256) int_canon;
  assert (a_minus_b == pow2_three s1 s2 s3 + s4 * pow2_192 - c * pow2_256);
  assert_by_tactic (pow2_three s1 s2 s3 + s4 * pow2_192 == pow2_four s1 s2 s3 s4) int_canon;
  () 
#pop-options

#push-options "--z3rlimit 3000 --max_fuel 0 --max_ifuel 0"
let lemma_sqr_part3
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
  =
  //admit();
  ()
#pop-options
