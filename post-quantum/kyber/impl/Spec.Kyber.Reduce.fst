module Spec.Kyber.Reduce

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Kyber.Params
open Spec.Kyber.Lemmas
open Spec.Powtwo.Lemmas

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lemma_montgomery_z2: 
    a:uint32 
  -> z2:uint32{uint_v z2 == (uint_v a * params_qinv % modulus U32) % pow2 params_logr} 
  -> Lemma (uint_v z2 == (uint_v a * params_qinv) % pow2 params_logr)

let lemma_montgomery_z2 a z2 =
  assert(modulus U32 == pow2 32);
  pow2_plus params_logr (32 - params_logr);
  assert(modulus U32 = pow2 params_logr * pow2 (32-params_logr));
  assert(uint_v z2 == (uint_v a * params_qinv % (pow2 params_logr * pow2 (32-params_logr))) % pow2 params_logr);
  modulo_modulo_lemma (uint_v a * params_qinv) (pow2 params_logr) (pow2 (32-params_logr))

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lemma_montgomery_a2_mod_r_eq_0: 
    a:uint32 
  -> z2:uint32{uint_v z2 == (uint_v a * params_qinv) % pow2 params_logr} 
  -> a2:uint32{uint_v a2 == uint_v a + uint_v (z2) * params_q} 
  -> Lemma( uint_v a2 % pow2 params_logr == 0)

let lemma_montgomery_a2_mod_r_eq_0 a z2 a2 =
  assert(uint_v a2 == uint_v a + ((uint_v a * params_qinv) % pow2 params_logr) * params_q);
  lemma_mod_add_distr (uint_v a) (((uint_v a * params_qinv) % pow2 params_logr) * params_q) (pow2 params_logr);
  (*assert (uint_v a2 % pow2 params_logr == (uint_v a + (((uint_v a * params_qinv) % pow2 params_logr) * params_q) % pow2 params_logr) % pow2 params_logr);
  *)
  lemma_mod_mul_distr_l (uint_v a * params_qinv) params_q (pow2 params_logr);
  lemma_mod_add_distr (uint_v a) (uint_v a * params_qinv * params_q) (pow2 params_logr);
  (*assert(uint_v a + (((uint_v a * params_qinv) % pow2 params_logr) * params_q ) % pow2 params_logr == uint_v a + (uint_v a * params_qinv * params_q) % pow2 params_logr);
  assert((uint_v a + (((uint_v a * params_qinv) % pow2 params_logr) * params_q ) % pow2 params_logr) % pow2 params_logr == (uint_v a + uint_v a * params_qinv * params_q) % pow2 params_logr);*)
  assert(uint_v a2 % pow2 params_logr == (uint_v a * (1+params_qinv*params_q)) % pow2 params_logr);
  
  assert((1+params_qinv*params_q) % (pow2 params_logr) == 0);
  lemma_mod_mul_distr_l (uint_v a) (1+params_qinv*params_q) (pow2 params_logr);
  assert(uint_v a2 % pow2 params_logr == 0)

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val montgomery_reduce: 
    a:uint32{uint_v a < modulus U32 - params_q * (pow2 params_logr)}
  -> u:uint16{uint_v u < pow2 (32-params_logr) /\ (uint_v u * pow2 params_logr) % params_q == uint_v a % params_q} 

let montgomery_reduce a =
  let z1 = a *. (u32 params_qinv) in
  assert(uint_v z1 = uint_v a * params_qinv % modulus U32);
  
  let z2 = z1 &. (u32 1 <<. size params_logr) -. u32 1 in
  modulo_pow2_u32 z1 params_logr;
  assert(uint_v z2 == (uint_v a * params_qinv % modulus U32) % pow2 params_logr);
  
  lemma_montgomery_z2 a z2;

  let a2 = a +. (z2 *. (u32 params_q)) in
  assert(uint_v (z2 *. (u32 params_q)) == (uint_v z2) * params_q);
  assert(uint_v a2 == uint_v a + uint_v (z2) * params_q);
  lemma_mod_plus (uint_v a) (uint_v z2) params_q;
  assert (uint_v a2 % params_q == uint_v a % params_q);

  lemma_montgomery_a2_mod_r_eq_0 a z2 a2;
  
  let out = a2 >>. size params_logr in
  lemma_div_mod (uint_v a2) (pow2 params_logr);
  assert(uint_v a2 == (uint_v a2 / pow2 params_logr) * pow2 params_logr);
  assert(uint_v out == uint_v a2 / pow2 params_logr);
  assert(uint_v out * pow2 params_logr == uint_v a2);
  
  assert(uint_v out < modulus U32 / pow2 params_logr);
  assert(modulus U32 == pow2 32);
  pow2_minus 32 params_logr;
  assert(uint_v out < pow2 (32 - params_logr));
  to_u16 out

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lemma_barrett: 
    a:uint16
  -> a2:uint16{uint_v a2 = (uint_v a * (pow2 16 / params_q)) / pow2 16}
  -> r:uint16{uint_v r = uint_v a - uint_v a2 * params_q}
  -> Lemma (uint_v r < params_q + (params_q * uint_v a) / pow2 16)

let lemma_barrett a a2 r =
  let sinv = pow2 16 / params_q in
  assert(pow2 16 * uint_v r = pow2 16 * (uint_v a) - (params_q *(uint_v a2 * pow2 16)));
  assert(pow2 16 * uint_v r = pow2 16 * (uint_v a) - (params_q * (uint_v a * sinv - ((uint_v a * sinv)%(pow2 16)))));
  assert(pow2 16 * uint_v r = pow2 16 * (uint_v a) - uint_v a * params_q * sinv + params_q * ((uint_v a * sinv)%(pow2 16)));
  assert(pow2 16 * uint_v r = pow2 16 * (uint_v a) - uint_v a * (pow2 16 - (pow2 16 % params_q)) + params_q * ((uint_v a * sinv)%(pow2 16)));
  assert(pow2 16 * uint_v r = uint_v a * (pow2 16 % params_q) + params_q * ((uint_v a * sinv)%(pow2 16)));
  assert(pow2 16 % params_q < params_q);
  assert ((uint_v a * sinv) % pow2 16 < pow2 16);
  lemma_mult_lt_right (uint_v a) (pow2 16 % params_q) (params_q);
  lemma_mult_lt_right params_q ((uint_v a * sinv) % pow2 16) (pow2 16);
  assert(pow2 16 * uint_v r < params_q * uint_v a + params_q * pow2 16);
  lemma_div_le (pow2 16 * uint_v r) (params_q * uint_v a + params_q * pow2 16) (pow2 16);
  division_addition_lemma (params_q * uint_v a) (pow2 16) params_q;
  cancel_mul_div (uint_v r) (pow2 16)
  
#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val barrett_reduce:
    a:uint16
  -> res:uint16{uint_v res % params_q == uint_v a % params_q /\ uint_v res < params_q + (params_q * uint_v a) / pow2 16}

let barrett_reduce a =
  let sinv = pow2 16 / params_q in
  assert (sinv * params_q <= pow2 16 /\ pow2 16 - params_q <= sinv * params_q);
  let a2 = to_u16 ((to_u32 a *. u32 sinv) >>. size 16) in 
  let res = a -. a2 *. u16 params_q in
  assert(uint_v res = uint_v a - uint_v a2 * params_q);
  lemma_mod_sub (uint_v a) params_q (uint_v a2);
  lemma_barrett a a2 res;
  res


#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"
  

val lemma_freeze_1: 
    a:uint16
  -> b:uint16
  -> c:uint16{uint_v c = 0 \/ uint_v c = maxint U16}
  -> Lemma (((uint_v c = 0) ==> uint_v (logand (logxor a b) c) == uint_v (uint #U16 #SEC 0)) /\ ((uint_v c = maxint U16) ==> uint_v (logand (logxor a b) c) == uint_v (logxor a b)))

let lemma_freeze_1 a b c =
  logand_lemma1 c (logxor a b)
  
#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lemma_freeze_2: 
    r:uint16 
  -> m:uint16
  -> c:uint16{uint_v c = 0 \/ uint_v c = maxint U16}
  -> Lemma ((uint_v c == 0 ==> logxor m (logand (logxor r m) c) == m) /\ (uint_v c == maxint U16 ==> logxor m (logand (logxor r m) c) == r))

let lemma_freeze_2 r m c =
  lemma_freeze_1 r m c;
  logxor_lemma m r
  

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val freeze :
    x:uint16
  -> res:uint16{uint_v res = uint_v x % params_q}

let freeze x =
  let r = barrett_reduce x in
  let m:uint16 = r -. u16 params_q in
  assert((uint_v r >= params_q) ==> (uint_v m = uint_v x % params_q));
  assert ((uint_v r < params_q) ==> (uint_v m >= pow2 16 - params_q));
  let c:uint16 = (m >>. size 15) *. u16 (pow2 16 - 1) in
  assert (uint_v r >= params_q ==> uint_v c = 0);
  assert(uint_v r < params_q ==> uint_v c = maxint U16);
  let res = logxor m (logand (logxor r m) c) in
  lemma_freeze_2 r m c;
  assert(uint_v r >= params_q ==> uint_v res = uint_v x % params_q);
  assert (uint_v r < params_q ==> uint_v res = uint_v x % params_q);
  res
