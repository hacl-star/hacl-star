module Vale.Curve25519.FastMul_helpers

open Vale.Def.Words_s
open Vale.Def.Types_s
open FStar.Mul
open FStar.Tactics
open FStar.Tactics.CanonCommSemiring
open Vale.Curve25519.Fast_defs
open Vale.Curve25519.Fast_lemmas_internal
open FStar.Math.Lemmas
#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"

#push-options "--z3rlimit 10"
let lemma_mul_pow2_bound (b:nat{b > 1}) (x y:natN (pow2 b))
  : Lemma (x * y < pow2 (2*b) - 1 /\
           x * y <= pow2 (2*b) - 2*pow2(b) + 1)
  = lemma_mul_bounds_le x (pow2 b - 1) y (pow2 b -1);
    pow2_plus b b;
    assert ( (pow2 b - 1) * (pow2 b -1) = pow2 (2*b) - 2*pow2(b) + 1)
#pop-options

let lemma_mul_bound64 (x y:nat64)
  : Lemma (x * y < pow2_128 - 1 /\ x * y <= pow2_128 - 2*pow2_64 + 1)
  = assert_norm (pow2 64 == pow2_64);
    assert_norm (pow2 128 == pow2_128);
    lemma_mul_pow2_bound 64 x y

(* Intel manual mentions this fact *)
let lemma_intel_prod_sum_bound (w x y z:nat64)
  : Lemma (w * x + y + z < pow2_128)
  = lemma_mul_bound64 w x

let lemma_prod_bounds (dst_hi dst_lo x y:nat64)
  : Lemma
    (requires
      pow2_64 * dst_hi + dst_lo == x * y)
    (ensures
      dst_hi < pow2_64 - 1 /\
      (dst_hi < pow2_64 - 2 \/
       dst_lo <= 1))
  = let result = x * y in
    lemma_div_mod result pow2_64;
    //assert (result = pow2_64 * (result / pow2_64) + result % pow2_64);
    //assert (result % pow2_64 == dst_lo);
    //assert (result / pow2_64 == dst_hi);
    lemma_mul_bound64 x y

let lemma_double_bound (x:nat64)
  : Lemma (add_wrap x x < pow2_64 - 1)
  = ()

type bit = b:nat { b <= 1 }

let lemma_offset_sum (a_agg:nat) (a0 a1 a2 a3 a4:nat64)
                     (b_agg:nat) (b0 b1 b2 b3 b4:nat64)
  : Lemma
    (requires
      a_agg = pow2_five a0 a1 a2 a3 a4 /\
      b_agg = pow2_five b0 b1 b2 b3 b4)
    (ensures
      a_agg + pow2_64 * b_agg =
      pow2_six a0 (a1 + b0) (a2 + b1) (a3 + b2) (a4 + b3) b4)
  = let lhs = a_agg + pow2_64 * b_agg in
    let rhs = pow2_six a0 (a1 + b0) (a2 + b1) (a3 + b2) (a4 + b3) b4 in
    assert_by_tactic (lhs == rhs) int_canon

#push-options "--z3rlimit 60"
let lemma_partial_sum
     (a0 a1 a2 a3 a4
      b0 b1 b2 b3 b4
      s1 s2 s3 s4 s5 c:nat64)
  : Lemma
    (requires
      (let s1', c1 = add_carry a1 b0 0 in
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
  (ensures
    pow2_six a0 (a1 + b0) (a2 + b1) (a3 + b2) (a4 + b3) b4 =
    pow2_seven a0 s1 s2 s3 s4 s5 c)
  = ()

let lemma_partial_sum_a2b
     (a0 a1 a2 a3 a4 a5
      b0 b1 b2 b3 b4
      s1 s2 s3 s4 s5:nat64)
  : Lemma
    (requires
      (let s1', c1 = add_carry a2 b0 0 in
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
  (ensures
    pow2_seven a0 a1 (a2 + b0) (a3 + b1) (a4 + b2) (a5 + b3) b4 =
    pow2_seven a0 a1 s1 s2 s3 s4 s5)
  = ()

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

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from 'FStar.Pervasives Prims Vale.Def.Words_s Vale.Curve25519.Fast_defs'"
val lemma_sqr (a:int) (a0 a1 a2 a3
               r8 r9 r10 r11 r12 r13 rax rcx
               r8' r9' r10' r11' r12' r13' r14'
               d0 d1 d2 d3 d4 d5 d6 d7:nat64) (cf:bit)
  : Lemma
    (requires
      a = pow2_four a0 a1 a2 a3 /\
      pow2_six r8 r9 r10 r11 r12 r13 ==
        pow2_five (mul_nats a0 a1)
                  (mul_nats a0 a2)
                  (mul_nats a0 a3)
                  (mul_nats a1 a3)
                  (mul_nats a2 a3) /\
      pow2_64 * rcx + rax == a1 * a2 /\
      pow2_seven r8' r9' r10' r11' r12' r13' r14' ==
        pow2_six (2*r8)
                 (2*r9)
                 (2*(r10+rax))
                 (2*(r11+rcx))
                 (2*r12)
                 (2*r13) /\
      pow2_nine d0 d1 d2 d3 d4 d5 d6 d7 cf ==
        pow2_eight (mul_nats a0 a0)
                   r8'
                   ((mul_nats a1 a1) + r9')
                   r10'
                   ((mul_nats a2 a2) + r11')
                   r12'
                   ((mul_nats a3 a3) + r13')
                   r14')
  (ensures
    a*a == pow2_eight d0 d1 d2 d3 d4 d5 d6 d7)
#set-options "--__temp_fast_implicits" //this flag should be the default for use with tactics, but isn't yet
let lemma_sqr a a0 a1 a2 a3
                r8 r9 r10 r11 r12 r13 rax rcx
                r8' r9' r10' r11' r12' r13' r14'
                d0 d1 d2 d3 d4 d5 d6 d7
              cf =
  assert (a < pow2_256); // PASSES
  assert_norm (pow2_256 == pow2 256); // PASSES
  pow2_plus 256 256;
  lemma_mul_pow2_bound 256 a a;
  assert (a*a < pow2_256 * pow2_256); // PASSES
  assert (cf = 1 ==> pow2_nine d0 d1 d2 d3 d4 d5 d6 d7 cf >= pow2_512);
  assert_by_tactic ((pow2_four a0 a1 a2 a3) * (pow2_four a0 a1 a2 a3) == pow2_seven (mul_nats a0 a0) (2*(mul_nats a0 a1)) (2*(mul_nats a0 a2) + (mul_nats a1 a1))
                                      (2*((mul_nats a0 a3) + (mul_nats a1 a2))) (2*(mul_nats a1 a3) + (mul_nats a2 a2)) (2*(mul_nats a2 a3)) (mul_nats a3 a3))
    (fun _ -> int_canon (); trefl(); qed ());
  let lhs:int = pow2_eight (mul_nats a0 a0) r8' ((mul_nats a1 a1) + r9') r10' ((mul_nats a2 a2) + r11') r12' ((mul_nats a3 a3) + r13') r14' in
  let squares = pow2_eight (mul_nats a0 a0) 0 (mul_nats a1 a1) 0 (mul_nats a2 a2) 0 (mul_nats a3 a3) 0 in
  let regs = pow2_eight 0 r8' r9' r10' r11' r12' r13' r14' in
  let rhs:int = squares + regs in
  assert (2*(mul_nats a0 a3 + a1*a2) >= 0);
  calc
    (eq2 #int) {
      pow2_eight
        (mul_nats a0 a0)
        r8'
        ((mul_nats a1 a1) + r9')
        r10'
        ((mul_nats a2 a2) + r11')
        r12'
        ((mul_nats a3 a3) + r13')
        r14';
    (eq2 #int ) { _ by (int_canon()) }
      pow2_eight
        (mul_nats a0 a0)
        0
        (mul_nats a1 a1)
        0
        (mul_nats a2 a2)
        0
        (mul_nats a3 a3)
        0
      + pow2_eight 0 r8' r9' r10' r11' r12' r13' r14';
    (eq2 #int) {
               calc
                 (eq2 #int) {
                    pow2_eight 0 r8' r9' r10' r11' r12' r13' r14';
                 (eq2 #int) { () }
                    pow2_64 * pow2_six (2*r8) (2*r9) (2*(r10+rax)) (2*(r11+rcx)) (2*r12) (2*r13);
                 (eq2 #int) {
                              calc
                                (eq2 #int) {
                                   pow2_six (2*r8) (2*r9) (2*(r10+rax)) (2*(r11+rcx)) (2*r12) (2*r13);
                                (eq2 #int) { () }
                                   2 * pow2_six r8 r9 (r10+rax) (r11+rcx) r12 r13;
                                (eq2 #int) { () }
                                           //   calc
                                           //     (eq2 #int) {
                                           //        pow2_six r8 r9 (r10+rax) (r11+rcx) r12 r13;
                                           //     (eq2 #int) { _ by (int_canon()) }
                                           //        pow2_six r8 r9 r10 r11 r12 r13 + pow2_six 0 0 rax rcx 0 0;
                                           //     (eq2 #int) { admit() }
                                           //        pow2_six (mul_nats a0 a1) (mul_nats a0 a2) (mul_nats a0 a3) (mul_nats a1 a3) (mul_nats a2 a3) 0
                                           //        + pow2_six 0 0 rax rcx 0 0;
                                           //     (eq2 #int) {
                                           //                   calc
                                           //                     (eq2 #int) {
                                           //                       pow2_six 0 0 rax rcx 0 0;
                                           //                     (eq2 #int) { () }
                                           //                       pow2_six 0 0 (a1*a2) 0 0 0;
                                           //                   }
                                           //                 }
                                           //        pow2_six (mul_nats a0 a1) (mul_nats a0 a2) (mul_nats a0 a3) (mul_nats a1 a3) (mul_nats a2 a3) 0
                                           //        + pow2_six 0 0 (a1*a2) 0 0 0;
                                           //     (eq2 #int) { admit () }
                                           //        pow2_six (mul_nats a0 a1) (mul_nats a0 a2) (mul_nats a0 a3 + a1*a2) (mul_nats a1 a3) (mul_nats a2 a3) 0;
                                           //   }
                                           // }
                                   2*pow2_six (mul_nats a0 a1) (mul_nats a0 a2) (mul_nats a0 a3 + a1*a2) (mul_nats a1 a3) (mul_nats a2 a3) 0;
                                (eq2 #int) {  () }
                                   pow2_six (2*(mul_nats a0 a1)) (2*(mul_nats a0 a2)) (2*(mul_nats a0 a3 + a1*a2)) (2*(mul_nats a1 a3)) (2*(mul_nats a2 a3)) 0;
                               }
                            }
                    pow2_64 * pow2_six (2*(mul_nats a0 a1)) (2*(mul_nats a0 a2)) (2*(mul_nats a0 a3 + a1*a2)) (2*(mul_nats a1 a3)) (2*(mul_nats a2 a3)) 0;
                 (eq2 #int) { () }
                    pow2_seven 0 (2*(mul_nats a0 a1)) (2*(mul_nats a0 a2)) (2*(mul_nats a0 a3 + a1*a2)) (2*(mul_nats a1 a3)) (2*(mul_nats a2 a3)) 0;
               }
             }
      pow2_eight
        (mul_nats a0 a0)
        (2*(mul_nats a0 a1))
        ((2*(mul_nats a0 a2)) + mul_nats a1 a1)
        (2*(mul_nats a0 a3 + a1*a2))
        ((2*(mul_nats a1 a3))
      + mul_nats a2 a2) (2*(mul_nats a2 a3)) (mul_nats a3 a3) 0;
    (eq2 #int) { () }
      pow2_seven
        (mul_nats a0 a0)
        (2*(mul_nats a0 a1))
        ((2*(mul_nats a0 a2)) + mul_nats a1 a1)
        (2*(mul_nats a0 a3 + a1*a2))
        ((2*(mul_nats a1 a3)) + mul_nats a2 a2)
        (2*(mul_nats a2 a3))
        (mul_nats a3 a3);
   };
  assert (pow2_nine d0 d1 d2 d3 d4 d5 d6 d7 cf == a*a);  // PASSES
  //assert (cf == 0);
  let ultimate_rhs:int = pow2_eight d0 d1 d2 d3 d4 d5 d6 d7 in
  assert_by_tactic (pow2_nine d0 d1 d2 d3 d4 d5 d6 d7 cf == ultimate_rhs) int_canon
