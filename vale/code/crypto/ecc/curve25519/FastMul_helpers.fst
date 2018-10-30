module FastMul_helpers

open Words_s
open Types_s
open FStar.Mul
open FStar.Tactics
open CanonCommSemiring

unfold let pow2_192 = 0x1000000000000000000000000000000000000000000000000
let _ = assert_norm (pow2 192 = pow2_192)
unfold let pow2_256 = 0x10000000000000000000000000000000000000000000000000000000000000000
let _ = assert_norm (pow2 256 = pow2_256)
unfold let pow2_320 = 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000
let _ = assert_norm (pow2 320 = pow2_320)
unfold let pow2_384 = 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
let _ = assert_norm (pow2 384 = pow2_384)
unfold let pow2_448 = 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
let _ = assert_norm (pow2 448 = pow2_448)
unfold let pow2_512 = 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
let _ = assert_norm (pow2 512 = pow2_512)

let int_canon = fun _ -> canon_semiring int_cr //; dump "Final"

//let my_bool_to_nat (b:bool) : nat = if b then 1 else 0

//unfold let assert_by_tactic = assert_by_tactic

let pow2_two (c0 c1:nat) : nat = c0 + pow2_64 * c1
let pow2_three (c0 c1 c2:nat) : nat = pow2_two c0 c1 + pow2_128 * c2
let pow2_four (c0 c1 c2 c3:nat) : nat = pow2_three c0 c1 c2 + pow2_192 * c3
let pow2_five (c0 c1 c2 c3 c4:nat) : nat = pow2_four c0 c1 c2 c3 + pow2_256 * c4
let pow2_six (c0 c1 c2 c3 c4 c5:nat) : nat = pow2_five c0 c1 c2 c3 c4 + pow2_320 * c5
let pow2_seven (c0 c1 c2 c3 c4 c5 c6:nat) : nat = pow2_six c0 c1 c2 c3 c4 c5 + pow2_384 * c6
let pow2_eight (c0 c1 c2 c3 c4 c5 c6 c7:nat) : nat = pow2_seven c0 c1 c2 c3 c4 c5 c6 + pow2_448 * c7
let pow2_nine (c0 c1 c2 c3 c4 c5 c6 c7 c8:nat) : nat = pow2_eight c0 c1 c2 c3 c4 c5 c6 c7 + pow2_512 * c8

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




type bit = b:nat { b <= 1 }

let bool_bit (b:bool) : bit = if b then 1 else 0

open Arch.Types
let add_carry (x y:nat64) (c:bit) : nat64 & (c':nat{c = 0 || c = 1})
  =
  add_wrap64 (add_wrap64 x y) c,
  (if x + y + c >= pow2_64 then 1 else 0)


let lemma_overflow (dst_hi dst_lo addend:nat64) (old_overflow:bit) : Lemma
  (requires dst_hi < pow2_64 - 1 /\
            (dst_hi < pow2_64 - 2 \/ dst_lo <= 1) /\
            addend < pow2_64 - 1 /\
            (old_overflow = 0 \/ addend < pow2_64 - 2))
  (ensures dst_hi < pow2_64 - 2 \/ dst_lo + addend + old_overflow < pow2_64)
  =
  ()

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
#pop-options
