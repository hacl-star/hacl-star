module Spec.Kyber.Reduce

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Kyber.Params
open Spec.Kyber.Lemmas
open Spec.Powtwo.Lemmas
open Spec.Kyber.Arithmetic

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lemma_montgomery_a2_mod_r_eq_0: 
    a:nat 
  -> z:nat{z = (a * params_qinv) % pow2 params_logr} 
  -> a2:nat{a2 = a + (z) * params_q} 
  -> Lemma( a2 % pow2 params_logr == 0)

let lemma_montgomery_a2_mod_r_eq_0 a z a2 =
  assert(a2 = a + ((a * params_qinv) % pow2 params_logr) * params_q);
  lemma_mod_add_distr a (((a * params_qinv) % pow2 params_logr) * params_q) (pow2 params_logr);
  (*assert ( a2 % pow2 params_logr == ( a + ((( a * params_qinv) % pow2 params_logr) * params_q) % pow2 params_logr) % pow2 params_logr);
  *)
  lemma_mod_mul_distr_l ( a * params_qinv) params_q (pow2 params_logr);
  lemma_mod_add_distr ( a) ( a * params_qinv * params_q) (pow2 params_logr);
  (*assert( a + ((( a * params_qinv) % pow2 params_logr) * params_q ) % pow2 params_logr ==  a + ( a * params_qinv * params_q) % pow2 params_logr);
  assert(( a + ((( a * params_qinv) % pow2 params_logr) * params_q ) % pow2 params_logr) % pow2 params_logr == ( a +  a * params_qinv * params_q) % pow2 params_logr);*)
  assert( a2 % pow2 params_logr == ( a * (1+params_qinv*params_q)) % pow2 params_logr);
  
  assert((1+params_qinv*params_q) % (pow2 params_logr) == 0);
  lemma_mod_mul_distr_l ( a) (1+params_qinv*params_q) (pow2 params_logr);
  assert( a2 % pow2 params_logr == 0)

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val montgomery_reduce: 
    a:nat{ a < pow2 32 - params_q * (pow2 params_logr)}
  -> u:nat{ u < pow2 (32-params_logr) /\ ( u * pow2 params_logr) % params_q ==  a % params_q} 

let montgomery_reduce a =
  let z = (a * params_qinv) % pow2 params_logr in
  let a2 = a + (z * params_q) in
  lemma_mod_plus ( a) (z) params_q;
  lemma_montgomery_a2_mod_r_eq_0 a z a2;
  
  let out = a2 / pow2 params_logr in
  lemma_div_mod ( a2) (pow2 params_logr);
  assert( a2 == ( a2 / pow2 params_logr) * pow2 params_logr);
  assert( out ==  a2 / pow2 params_logr);
  assert( out * pow2 params_logr ==  a2);
  
  assert( out < modulus U32 / pow2 params_logr);
  assert(modulus U32 == pow2 32);
  pow2_minus 32 params_logr;
  assert( out < pow2 (32 - params_logr));
  out

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lemma_barrett: 
    a:nat
  -> a2:nat{ a2 = ( a * (pow2 16 / params_q)) / pow2 16}
  -> r:nat{ r =  a -  a2 * params_q}
  -> Lemma ( r < params_q + (params_q *  a) / pow2 16)

let lemma_barrett a a2 r =
  let sinv = pow2 16 / params_q in
  assert(pow2 16 *  r = pow2 16 * ( a) - (params_q *( a2 * pow2 16)));
  assert(pow2 16 *  r = pow2 16 * ( a) - (params_q * ( a * sinv - (( a * sinv)%(pow2 16)))));
  assert(pow2 16 *  r = pow2 16 * ( a) -  a * params_q * sinv + params_q * (( a * sinv)%(pow2 16)));
  assert(pow2 16 *  r = pow2 16 * ( a) -  a * (pow2 16 - (pow2 16 % params_q)) + params_q * (( a * sinv)%(pow2 16)));
  assert(pow2 16 *  r =  a * (pow2 16 % params_q) + params_q * (( a * sinv)%(pow2 16)));
  assert(pow2 16 % params_q < params_q);
  assert (( a * sinv) % pow2 16 < pow2 16);
  lemma_mult_lt_right ( a) (pow2 16 % params_q) (params_q);
  lemma_mult_lt_right params_q (( a * sinv) % pow2 16) (pow2 16);
  assert(pow2 16 *  r < params_q *  a + params_q * pow2 16);
  lemma_div_le (pow2 16 *  r) (params_q *  a + params_q * pow2 16) (pow2 16);
  division_addition_lemma (params_q *  a) (pow2 16) params_q;
  cancel_mul_div ( r) (pow2 16)
  
#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val barrett_reduce:
    a:nat{a<pow2 16}
  -> res:nat{ res % params_q ==  a % params_q /\  res < params_q + (params_q *  a) / pow2 16}

let barrett_reduce a =
  let sinv = pow2 16 / params_q in
  assert (sinv * params_q <= pow2 16 /\ pow2 16 - params_q <= sinv * params_q);
  let a2 = (a * sinv) / pow2 16 in 
  let res = a - a2 * params_q in
  lemma_mod_sub ( a) params_q ( a2);
  lemma_barrett a a2 res;
  res
  

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val freeze :
    x:nat{x<pow2 16}
  -> res:nat{ res =  x % params_q}

let freeze x =
  let r = barrett_reduce x in
  let m = r - params_q in
  if r >= params_q then m else r
