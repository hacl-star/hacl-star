module FastSqr_helpers

open Words_s
open Types_s
open FStar.Mul
open FStar.Tactics
open CanonCommSemiring

open Fast_defs
open Fast_lemmas

open FStar.Math.Lemmas 

let int_canon = fun _ -> canon_semiring int_cr //; dump "Final"

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

