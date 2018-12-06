module FastMul_helpers

open Words_s
open Types_s
open FStar.Mul
open FStar.Tactics
open CanonCommSemiring
open Fast_defs

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection -CanonCommMonoid -CanonCommSwaps -CanonCommSemiring'"

(*
let simple_helper2 (a0 b0 b1 a0b0_lo a0b0_hi a0b1_lo a0b1_hi sum:nat64) (overflow:bool) : Lemma
  (requires pow2_two a0b0_lo a0b0_hi = a0 * b0 /\
            pow2_two a0b1_lo a0b1_hi = a0 * b1 /\
            sum == add_wrap (add_wrap a0b1_lo a0b0_hi) 0 /\
            overflow == (a0b1_lo + a0b0_hi >= pow2_64))
  (ensures (let b = pow2_two b0 b1 in
            let overflow_v = if overflow then 1 else 0 in
            a0 * b == pow2_three a0b0_lo sum (a0b1_hi + overflow_v)))
  =
  let b = pow2_two b0 b1 in
  let overflow_v = if overflow then 1 else 0 in
  let lhs = a0 * b in
  let rhs = pow2_three a0b0_lo sum (a0b1_hi + overflow_v) in
  assert_by_tactic (lhs == rhs) int_canon;
  ()

let a0b_helper (a0 b0 b1 b2 b3 
                a0b0_lo a0b0_hi 
                a0b1_lo a0b1_hi 
                a0b2_lo a0b2_hi 
                a0b3_lo a0b3_hi 
                sum0 sum1 sum2 :nat64) (overflow0 overflow1 overflow2:bool) : Lemma
  (requires pow2_64 * a0b0_hi + a0b0_lo == a0 * b0 /\
            pow2_64 * a0b1_hi + a0b1_lo == a0 * b1 /\
            pow2_64 * a0b2_hi + a0b2_lo == a0 * b2 /\
            pow2_64 * a0b3_hi + a0b3_lo == a0 * b3 /\
            sum0 == add_wrap (add_wrap a0b1_lo a0b0_hi) 0 /\
            overflow0 == (a0b1_lo + a0b0_hi >= pow2_64) /\
            (let carry0 = if overflow0 then 1 else 0 in
            sum1 == add_wrap (add_wrap a0b2_lo a0b1_hi) carry0 /\
            overflow1 == (a0b2_lo + a0b1_hi + carry0 >= pow2_64) /\
            (let carry1 = if overflow1 then 1 else 0 in
            sum2 == add_wrap (add_wrap a0b3_lo a0b2_hi) carry1 /\
            overflow2 == (a0b3_lo + a0b2_hi + carry1 >= pow2_64))))
  (ensures (let b = b0 + pow2_64 * b1 + pow2_128 * b2 + pow2_192 * b3 in
            let carry2 = if overflow2 then 1 else 0 in
            a0 * b == a0b0_lo + pow2_64 * sum0 + pow2_128 * sum1 + pow2_192 * sum2 + pow2_256 * (a0b3_hi + carry2)))
  =
  let b = b0 + pow2_64 * b1 + pow2_128 * b2 + pow2_192 * b3 in
  let carry2 = if overflow2 then 1 else 0 in
  let lhs = a0 * b in
  let rhs = a0b0_lo + pow2_64 * sum0 + pow2_128 * sum1 + pow2_192 * sum2 + pow2_256 * (a0b3_hi + carry2) in
  assert_by_tactic (lhs == rhs)
    int_canon;
  ()
*)
open FStar.Math.Lemmas

let lemma_mul_bounds_le (x b_x y b_y:nat) : Lemma 
  (requires x <= b_x /\ y <= b_y)
  (ensures x * y <= b_x * b_y)
  =
  lemma_mult_le_right b_x y b_y;
  lemma_mult_le_right y x b_x;
  ()

let mul_nats (x y:nat) : nat = 
  let prod = x * y in
  lemma_mul_bounds_le 0 x 0 y;
  prod

#push-options "--z3rlimit 10"
let lemma_mul_pow2_bound (b:nat{b > 1}) (x y:natN (pow2 b)) :
  Lemma (x * y < pow2 (2*b) - 1 /\
         x * y <= pow2 (2*b) - 2*pow2(b) + 1)
  =
  lemma_mul_bounds_le x (pow2 b - 1) y (pow2 b -1);
  pow2_plus b b;
  assert ( (pow2 b - 1) * (pow2 b -1) = pow2 (2*b) - 2*pow2(b) + 1);
  ()
#pop-options

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


type bit = b:nat { b <= 1 }


let lemma_offset_sum (a_agg:nat) (a0 a1 a2 a3 a4:nat64)
                      (b_agg:nat) (b0 b1 b2 b3 b4:nat64) : Lemma
  (requires a_agg = pow2_five a0 a1 a2 a3 a4 /\           
            b_agg = pow2_five b0 b1 b2 b3 b4)
  (ensures a_agg + pow2_64 * b_agg = 
           pow2_six a0 (a1 + b0) (a2 + b1) (a3 + b2) (a4 + b3) b4)
  =
  let lhs = a_agg + pow2_64 * b_agg in
  let rhs = pow2_six a0 (a1 + b0) (a2 + b1) (a3 + b2) (a4 + b3) b4 in
  assert_by_tactic (lhs == rhs) int_canon;
  ()


#push-options "--z3rlimit 60"
let lemma_partial_sum (
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
  =
  ()

let lemma_partial_sum_a2b (
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
  =
  ()

let lemma_partial_sum_a3b (
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
  =
  ()
#pop-options

let lemma_sum_a1b
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
  =
  assert_by_tactic (
    (pow2_two a0 a1) * b == 
    pow2_two (mul_nats a0 b) (mul_nats a1 b)) int_canon; 
  assert (
    pow2_two (mul_nats a0 b) (mul_nats a1 b) ==
    pow2_two a0b a1b);
  lemma_offset_sum a0b a0b_0 a0b_1 a0b_2 a0b_3 a0b_4
                   a1b a1b_0 a1b_1 a1b_2 a1b_3 a1b_4;
  assert (
    pow2_two a0b a1b ==
    pow2_six a0b_0 (a0b_1 + a1b_0) (a0b_2 + a1b_1) (a0b_3 + a1b_2) (a0b_4 + a1b_3) a1b_4);
  lemma_partial_sum a0b_0 a0b_1 a0b_2 a0b_3 a0b_4
                    a1b_0 a1b_1 a1b_2 a1b_3 a1b_4
                    s1 s2 s3 s4 s5 c;
  ()

#push-options "--z3rlimit 60"
let lemma_sum_a2b
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
  =
  
  assert_by_tactic (
    (pow2_three a0 a1 a2) * b == 
    mul_nats (pow2_two a0 a1) b + pow2_128 * (mul_nats a2 b)) int_canon;
  assert (
    mul_nats (pow2_two a0 a1) b + pow2_128 * (mul_nats a2 b) ==
    a0a1b + pow2_128 * a2b);
  assert_by_tactic (
    a0a1b + pow2_128 * a2b ==
    pow2_seven a0a1b_0 a0a1b_1 (a0a1b_2 + a2b_0) (a0a1b_3 + a2b_1) (a0a1b_4 + a2b_2) (a0a1b_5 + a2b_3) a2b_4) int_canon;
  lemma_partial_sum_a2b
        a0a1b_0 a0a1b_1 a0a1b_2 a0a1b_3 a0a1b_4 a0a1b_5
        a2b_0 a2b_1 a2b_2 a2b_3 a2b_4
        s1 s2 s3 s4 s5;
  ()


let lemma_sum_a3b
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
  =
  
  assert_by_tactic (
    (pow2_four a0 a1 a2 a3) * b == 
    mul_nats (pow2_three a0 a1 a2) b + pow2_192 * (mul_nats a3 b)) int_canon;
  assert (
    mul_nats (pow2_three a0 a1 a2) b + pow2_192 * (mul_nats a3 b) ==
    a0a1a2b + pow2_192 * a3b);
  assert_by_tactic (
    a0a1a2b + pow2_192 * a3b ==
    pow2_eight a0a1a2b_0 a0a1a2b_1 a0a1a2b_2 (a0a1a2b_3 + a3b_0) (a0a1a2b_4 + a3b_1) (a0a1a2b_5 + a3b_2) (a0a1a2b_6 + a3b_3) a3b_4) int_canon;
  lemma_partial_sum_a3b
        a0a1a2b_0 a0a1a2b_1 a0a1a2b_2 a0a1a2b_3 a0a1a2b_4 a0a1a2b_5 a0a1a2b_6
        a3b_0 a3b_1 a3b_2 a3b_3 a3b_4
        s1 s2 s3 s4 s5;
  ()

#pop-options

let lemma_dbl_pow2_six (z0 z1 z2 z3 z4 z5:nat) :
  Lemma (2*pow2_six z0 z1 z2 z3 z4 z5 == pow2_six (2*z0) (2*z1) (2*z2) (2*z3) (2*z4) (2*z5))
  =
  ()
  
#push-options "--z3rlimit 20"
let lemma_sqr (a:int) (a0 a1 a2 a3 
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
  =
  assert (a < pow2_256); // PASSES
  assert_norm (pow2_256 == pow2 256); // PASSES
  pow2_plus 256 256;
  lemma_mul_pow2_bound 256 a a;
  assert (a*a < pow2_256 * pow2_256); // PASSES 
  assert (cf = 1 ==> pow2_nine d0 d1 d2 d3 d4 d5 d6 d7 cf >= pow2_512);

  // Fails here, but succeeds in Vale!?
  //assert_by_tactic (a*a == pow2_seven (mul_nats a0 a0) (2*(mul_nats a0 a1)) (2*(mul_nats a0 a2) + (mul_nats a1 a1))
  //                                    (2*((mul_nats a0 a3) + (mul_nats a1 a2))) (2*(mul_nats a1 a3) + (mul_nats a2 a2)) (2*(mul_nats a2 a3)) (mul_nats a3 a3)) int_canon;
  let lhs:int = pow2_eight (mul_nats a0 a0) r8' ((mul_nats a1 a1) + r9') r10' ((mul_nats a2 a2) + r11') r12' ((mul_nats a3 a3) + r13') r14' in
  let squares = pow2_eight (mul_nats a0 a0) 0 (mul_nats a1 a1) 0 (mul_nats a2 a2) 0 (mul_nats a3 a3) 0 in
  let regs = pow2_eight 0 r8' r9' r10' r11' r12' r13' r14' in
  let rhs:int = squares + regs in
  assert_by_tactic (lhs == rhs) int_canon; // PASSES

  assert_by_tactic (regs == pow2_64 * pow2_seven r8' r9' r10' r11' r12' r13' r14') int_canon;  // PASSES
  assert (pow2_64 * pow2_seven r8' r9' r10' r11' r12' r13' r14' == pow2_64 * pow2_six (2*r8) (2*r9) (2*(r10+rax)) (2*(r11+rcx)) (2*r12) (2*r13));  // PASSES
  assert_by_tactic (pow2_64 * pow2_six (2*r8) (2*r9) (2*(r10+rax)) (2*(r11+rcx)) (2*r12) (2*r13) == pow2_seven 0 (2*r8) (2*r9) (2*(r10+rax)) (2*(r11+rcx)) (2*r12) (2*r13)) int_canon; // PASSES
  lemma_dbl_pow2_six r8 r9 (r10+rax) (r11+rcx) r12 r13;
  assert (pow2_six (2*r8) (2*r9) (2*(r10+rax)) (2*(r11+rcx)) (2*r12) (2*r13) == 2 * pow2_six r8 r9 (r10+rax) (r11+rcx) r12 r13);  // PASSES
  assert_by_tactic (pow2_six r8 r9 (r10+rax) (r11+rcx) r12 r13 == pow2_six r8 r9 r10 r11 r12 r13 + pow2_six 0 0 rax rcx 0 0) int_canon;  // PASSES
  let larger:int = pow2_six  (mul_nats a0 a1) (mul_nats a0 a2) (mul_nats a0 a3) (mul_nats a1 a3) (mul_nats a2 a3) 0 in
  assert_by_tactic (pow2_five (mul_nats a0 a1) (mul_nats a0 a2) (mul_nats a0 a3) (mul_nats a1 a3) (mul_nats a2 a3) == larger) int_canon;  // PASSES
  let a1a2_six:int = pow2_six 0 0 (a1 * a2) 0 0 0 in
  assert_by_tactic (pow2_six 0 0 rax rcx 0 0 == a1a2_six) int_canon; // PASSES
  lemma_dbl_pow2_six (mul_nats a0 a1) (mul_nats a0 a2) (mul_nats a0 a3 + a1*a2) (mul_nats a1 a3) (mul_nats a2 a3) 0;
  assert_by_tactic (pow2_64 * pow2_six (2*(mul_nats a0 a1)) (2*(mul_nats a0 a2)) (2*(mul_nats a0 a3 + a1*a2)) (2*(mul_nats a1 a3)) (2*(mul_nats a2 a3)) 0 ==
                    pow2_seven 0 (2*(mul_nats a0 a1)) (2*(mul_nats a0 a2)) (2*(mul_nats a0 a3 + a1*a2)) (2*(mul_nats a1 a3)) (2*(mul_nats a2 a3)) 0) int_canon;  // PASSES
  assert_by_tactic (rhs == pow2_eight (mul_nats a0 a0) (2*(mul_nats a0 a1)) ((2*(mul_nats a0 a2)) + mul_nats a1 a1) (2*(mul_nats a0 a3 + a1*a2)) ((2*(mul_nats a1 a3)) + mul_nats a2 a2) (2*(mul_nats a2 a3)) (mul_nats a3 a3) 0) int_canon;  // PASSES
  let final_rhs:int = pow2_seven (mul_nats a0 a0) (2*(mul_nats a0 a1)) ((2*(mul_nats a0 a2)) + mul_nats a1 a1) (2*(mul_nats a0 a3 + a1*a2)) ((2*(mul_nats a1 a3)) + mul_nats a2 a2) (2*(mul_nats a2 a3)) (mul_nats a3 a3) in
  assert_by_tactic (pow2_eight (mul_nats a0 a0) (2*(mul_nats a0 a1)) ((2*(mul_nats a0 a2)) + mul_nats a1 a1) (2*(mul_nats a0 a3 + a1*a2)) ((2*(mul_nats a1 a3)) + mul_nats a2 a2) (2*(mul_nats a2 a3)) (mul_nats a3 a3) 0 ==
                    final_rhs) int_canon;   // PASSES
  assert (pow2_nine d0 d1 d2 d3 d4 d5 d6 d7 cf == a*a);  // PASSES
  assert (cf == 0);
  let ultimate_rhs:int = pow2_eight d0 d1 d2 d3 d4 d5 d6 d7 in
  assert_by_tactic (pow2_nine d0 d1 d2 d3 d4 d5 d6 d7 cf == ultimate_rhs) int_canon;
(*
  calc {
    pow2_nine d0 d1 d2 d3 d4 d5 d6 d7 cf

    pow2_eight (mul_nats a0 a0) r8' ((mul_nats a1 a1) + r9') r10' ((mul_nats a2 a2) + r11') r12' ((mul_nats a3 a3) + r13') r14')

    pow2_eight (mul_nats a0 a0) 0 (mul_nats a1 a1) 0 (mul_nats a2 a2) 0 (mul_nats a3 a3) 0 +
    pow2_eight 0 r8' r9' r10' r11' r12' r13' r14'

        calc {
            pow2_eight 0 r8' r9' r10' r11' r12' r13' r14'
            pow2_64 * pow2_six (2*r8) (2*r9) (2*(r10+rax)) (2*(r11+rcx)) (2*r12) (2*r13)
            calc {
                pow2_six (2*r8) (2*r9) (2*(r10+rax)) (2*(r11+rcx)) (2*r12) (2*r13)
                2 * pow2_six r8 r9 (r10+rax) (r11+rcx) r12 r13)
                calc {
                    pow2_six r8 r9 (r10+rax) (r11+rcx) r12 r13)
                    pow2_six r8 r9 r10 r11 r12 r13 
                        + pow2_six 0 0 rax rcx 0 0
                    pow2_six (mul_nats a0 a1) (mul_nats a0 a2) (mul_nats a0 a3) (mul_nats a1 a3) (mul_nats a2 a3) 0
                        + pow2_six 0 0 rax rcx 0 0
                    pow2_six (mul_nats a0 a1) (mul_nats a0 a2) (mul_nats a0 a3) (mul_nats a1 a3) (mul_nats a2 a3) 0
                        + pow2_six 0 0 (a1*a2) 0 0 0
                    pow2_six (mul_nats a0 a1) (mul_nats a0 a2) (mul_nats a0 a3 + a1*a2) (mul_nats a1 a3) (mul_nats a2 a3) 0
                }
                2*pow2_six (mul_nats a0 a1) (mul_nats a0 a2) (mul_nats a0 a3 + a1*a2) (mul_nats a1 a3) (mul_nats a2 a3) 0
                pow2_six (2*(mul_nats a0 a1)) (2*(mul_nats a0 a2)) (2*(mul_nats a0 a3 + a1*a2)) (2*(mul_nats a1 a3)) (2*(mul_nats a2 a3)) 0
            }
            pow2_64 * pow2_six (2*(mul_nats a0 a1)) (2*(mul_nats a0 a2)) (2*(mul_nats a0 a3 + a1*a2)) (2*(mul_nats a1 a3)) (2*(mul_nats a2 a3)) 0

            pow2_seven 0 (2*(mul_nats a0 a1)) (2*(mul_nats a0 a2)) (2*(mul_nats a0 a3 + a1*a2)) (2*(mul_nats a1 a3)) (2*(mul_nats a2 a3)) 0
        }
    pow2_eight (mul_nats a0 a0) (2*(mul_nats a0 a1)) ((2*(mul_nats a0 a2)) + mul_nats a1 a1) (2*(mul_nats a0 a3 + a1*a2)) ((2*(mul_nats a1 a3)) + mul_nats a2 a2) (2*(mul_nats a2 a3)) (mul_nats a3 a3) 0

    pow2_seven (mul_nats a0 a0) (2*(mul_nats a0 a1)) ((2*(mul_nats a0 a2)) + mul_nats a1 a1) (2*(mul_nats a0 a3 + a1*a2)) ((2*(mul_nats a1 a3)) + mul_nats a2 a2) (2*(mul_nats a2 a3)) (mul_nats a3 a3) 
}
*)
  ()
#pop-options  


let sub_carry (x y:nat64) (c:bit) : nat64 & (c':bit)
  =
  (x - (y + c)) % pow2_64,
  (if x - (y + c) < 0 then 1 else 0)

#reset-options "--z3rlimit 3000 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"
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
