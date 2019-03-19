module FastHybrid_helpers

open Words_s
open Types_s
open FStar.Mul
open FStar.Tactics
open FStar.Tactics.CanonCommSemiring
open Fast_defs
open Fast_lemmas_internal

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

let lemma_carry_prime (a0 a1 a2 a3 a0' a1' a2' a3' carry_in:nat64) (carry:bit) : Lemma
  (requires pow2_five a0' a1' a2' a3' carry == pow2_four a0 a1 a2 a3 + carry_in * 38 /\
            carry_in * 38 - 1 + 38 < pow2_64)
  (ensures a0' + carry * 38 < pow2_64 /\
           (pow2_four (a0' + carry * 38) a1' a2' a3') % prime == (pow2_four a0 a1 a2 a3 + carry_in * pow2_256) % prime)
  =
  assert (a0' + carry * 38 < pow2_64);

  calc (==) {
    (pow2_four a0 a1 a2 a3 + carry_in * pow2_256) % prime;
    == { lemma_mul_pow256_add (pow2_four a0 a1 a2 a3) carry_in }
    (pow2_four a0 a1 a2 a3 + carry_in * 38) % prime;
    == {}
    (pow2_five a0' a1' a2' a3' carry) % prime;
    == { _ by (int_canon()) }    
    (pow2_four a0' a1' a2' a3' + (carry * pow2_256)) % prime;
    == { lemma_mul_pow256_add (pow2_four a0' a1' a2' a3') carry }
    (pow2_four a0' a1' a2' a3' + (carry * 38)) % prime;
    == {  calc (==) {
            (pow2_four a0' a1' a2' a3') + (carry * 38);            
            == { _ by (int_canon()) }
            pow2_four (a0' + carry * 38) a1' a2' a3';
          }
       }
    (pow2_four (a0' + carry * 38) a1' a2' a3') % prime;
  };
  ()

#reset-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"
let lemma_fast_mul1 (a:nat) 
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
  =
  assert_by_tactic (b * pow2_four a0 a1 a2 a3 == pow2_four (b*a0) (b*a1) (b*a2) (b*a3)) int_canon;
  //lemma_prod_bounds ba0_hi ba0_lo b a0;
  //lemma_prod_bounds ba1_hi ba1_lo b a1;
  //lemma_prod_bounds ba2_hi ba2_lo b a2;
  //lemma_prod_bounds ba3_hi ba3_lo b a3;
  ()


let lemma_addition (a d:nat) (a0 a1 a2 a3 d0 d1 d2 d3 d4:nat64)
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
  =
  ()

let lemma_carry_wide (a0 a1 a2 a3 a4 a5 a6 a7
                      d0 d1 d2 d3 carry
                      d0' d1' d2' d3':nat64) : Lemma
  (requires pow2_five d0 d1 d2 d3 carry == 38 * pow2_four a4 a5 a6 a7 + pow2_four a0 a1 a2 a3 /\
            pow2_four d0' d1' d2' d3' % prime == ((pow2_four d0 d1 d2 d3) + carry * pow2_256) % prime)
  (ensures (pow2_four d0' d1' d2' d3') % prime == (pow2_eight a0 a1 a2 a3 a4 a5 a6 a7) % prime)
  =
  calc (==) {
    pow2_four d0' d1' d2' d3' % prime;
    == { calc (==) {
           (pow2_four d0 d1 d2 d3) + carry * pow2_256;
           == { _ by (int_canon()) }
           pow2_five d0 d1 d2 d3 carry;
         }
       }
    pow2_five d0 d1 d2 d3 carry % prime;
    == {}
    (pow2_four a0 a1 a2 a3 + 38 * pow2_four a4 a5 a6 a7) % prime;
    == { lemma_mul_pow256_add (pow2_four a0 a1 a2 a3) (pow2_four a4 a5 a6 a7) }
    (pow2_four a0 a1 a2 a3 + pow2_256 * pow2_four a4 a5 a6 a7) % prime;
    == { _ by (int_canon()) }
    (pow2_eight a0 a1 a2 a3 a4 a5 a6 a7) % prime;
  }


let pow2int_four (c0 c1 c2 c3:int) : int = c0 + c1 * pow2_64 + c2 * pow2_128 + c3 * pow2_192

#reset-options "--z3rlimit 10 --max_fuel 0 --max_ifuel 0 --using_facts_from '' --smtencoding.nl_arith_repr native"
let lemma_mul_pow256_sub (x y:nat) : 
  Lemma ((x - y * pow2_256) % prime == (x - y * 38) % prime)
  =
  assert_norm (pow2_256 % prime == 38);
  ()

#reset-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"
let lemma_carry_sub_prime (a0 a1 a2 a3 a0' a1' a2' a3' carry_in:nat64) (carry:bit) : Lemma
  (requires pow2_four a0' a1' a2' a3' - carry * pow2_256 == pow2_four a0 a1 a2 a3 - carry_in * 38 /\
            carry_in * 38 - 1 + 38 < pow2_64)
  (ensures a0' - carry * 38 >= 0 /\
           (pow2_four (a0' - carry * 38) a1' a2' a3') % prime == (pow2_four a0 a1 a2 a3 - carry_in * pow2_256) % prime)
  =  
  assert (a0' - carry * 38 >= 0);

  calc (==) {
    (pow2_four a0 a1 a2 a3 - carry_in * pow2_256) % prime;
    == { lemma_mul_pow256_sub (pow2_four a0 a1 a2 a3) carry_in }
    (pow2_four a0 a1 a2 a3 - carry_in * 38) % prime;
    == {}  
    (pow2_four a0' a1' a2' a3' - (carry * pow2_256)) % prime;
    == { lemma_mul_pow256_sub (pow2_four a0' a1' a2' a3') carry }
    (pow2_four a0' a1' a2' a3' - (carry * 38)) % prime;
    == {  calc (==) {
            (pow2_four a0' a1' a2' a3') - (carry * 38);            
            == { _ by (int_canon()) }
            pow2int_four (a0' - carry * 38) a1' a2' a3';
          }
       }
    (pow2_four (a0' - carry * 38) a1' a2' a3') % prime;
  };
  ()


let lemma_fmul (a0 a1 a2 a3 b d0 d1 d2 d3 carry:nat64) : Lemma
  (requires pow2_five d0 d1 d2 d3 carry == (pow2_four a0 a1 a2 a3) * b /\
            b < 131072)
  (ensures carry * 38 < pow2_63)
  =
  assert (pow2_four a0 a1 a2 a3 < pow2_256);
  assert_norm (131072 == pow2 17);  
  lemma_mul_bounds_le (pow2_four a0 a1 a2 a3) pow2_256 b (pow2 17);
  assert ((pow2_four a0 a1 a2 a3) * b <= pow2_256 * pow2 17);
  lemma_mul_bounds_le b b (pow2_four a0 a1 a2 a3) (pow2_four a0 a1 a2 a3);
  assert ((pow2_four a0 a1 a2 a3) * b <= pow2_256 * pow2 17)
