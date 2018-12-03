module FastMul_helpers

open Words_s
open Types_s
open FStar.Mul
open FStar.Tactics
open CanonCommSemiring
open Fast_defs


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
