module Spec.Kyber2.Reduce

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Kyber2.Params
open Spec.Kyber2.Lemmas
open Spec.Powtwo.Lemmas
open Lib.ModularArithmetic
open Lib.ModularArithmetic.Lemmas

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

(*val montgomery_reduce:
  a:int{a >= - params_q * pow2 (params_logr-1) /\ a < params_q * pow2 (params_logr-1)}
  -> Tot (t:int{t>= -params_q+1 /\ t<=params_q-1 /\ (t * pow2 params_logr) % params_q = a %params_q})

let montgomery_reduce a =
  let u' = (a*params_qinv) % pow2 params_logr in
  let u:int = if u' < pow2 (params_logr-1) then u' else u' - pow2 (params_logr) in
  assert_norm(u>= - pow2 (params_logr -1) /\ u < pow2 (params_logr-1) /\ u % pow2 params_logr = u');
  assert_norm ( - params_q * u > - params_q * pow2 (params_logr -1) /\ params_q * u <= params_q * pow2 (params_logr -1));
  let w = a - u * params_q in
  assert(w > -2 * params_q * pow2 (params_logr-1) /\ w < 2 * params_q * pow2 (params_logr-1));
  lemma_mod_plus a (-u) params_q;
  assert(w % params_q = a % params_q);
  lemma_mod_add_distr a (-(u * params_q)) (pow2 params_logr);
  lemma_mod_mul_distr_l (a*params_qinv) params_q (pow2 params_logr);
  assert ((u' * params_q) % pow2 params_logr = ((a * params_qinv)*params_q) % pow2 params_logr);
  paren_mul_left a params_qinv params_q;
  paren_mul_right a params_qinv params_q;
  assert(((a * params_qinv)*params_q) % pow2 params_logr = (a * (params_qinv*params_q)) % pow2 params_logr);
  lemma_mod_mul_distr_r a (params_qinv * params_q) (pow2 params_logr);
  assert_norm((params_qinv * params_q) % pow2 params_logr = 1);
  assert (((a * params_qinv)*params_q) % pow2 params_logr = a % pow2 params_logr);
  assert ((u' * params_q) % pow2 params_logr = a % pow2 params_logr);
  lemma_mod_mul_distr_l u params_q (pow2 params_logr);
  assert ((u * params_q) % pow2 params_logr = (u'*params_q) % pow2 params_logr);
  assert ((u * params_q) % pow2 params_logr = a % pow2 params_logr);
  lemma_mod_sub_distr a (u * params_q) (pow2 params_logr);
  assert (w % (pow2 params_logr) = (a - (a % pow2 params_logr)) % pow2 params_logr);
  lemma_mod_sub_distr a a (pow2 params_logr);
  assert (w % (pow2 params_logr) = 0);
  let t = w / (pow2 params_logr) in
  assert (w = t * (pow2 params_logr));
  t

*)
#reset-options "--z3rlimit 2000 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val montgomery_reduce_int32:
  a:int32{sint_v a >= - params_q * pow2 (params_logr-1) /\ sint_v a < params_q * pow2 (params_logr-1)}
  -> Tot (t:int16{sint_v t > - params_q /\ sint_v t < params_q /\ (sint_v t * pow2 params_logr) % params_q = sint_v a % params_q})

let montgomery_reduce_int32 a =
  let qinv = i32 (params_qinv) in
  let q = i32 (params_q) in
  let u = to_i16 (a *. qinv) in
  assert (sint_v u = ((sint_v a * params_qinv) @% pow2 32) @% pow2 16);
  assert (sint_v u % pow2 16 = ((sint_v a * params_qinv) @% pow2 32) % pow2 16);
  assert (sint_v (a*.qinv) % pow2 32 = (sint_v a * params_qinv) % pow2 32);
  pow2_plus 16 16;
  modulo_modulo_lemma (sint_v (a*.qinv)) (pow2 16) (pow2 16);
  assert (sint_v u % pow2 16 = ((sint_v a * params_qinv) % pow2 32) % pow2 16);
  modulo_modulo_lemma (sint_v a * params_qinv) (pow2 16) (pow2 16);
  assert (sint_v u = ((sint_v a * params_qinv) @% pow2 16)); 
  assert( - pow2 15 * params_q <= sint_v u * params_q /\ sint_v u * params_q < pow2 15 * params_q);
  pow2_double_mult 15;
  assert ( - pow2 16 * params_q < sint_v a - (sint_v u * params_q) /\ sint_v a - (sint_v u * params_q) < pow2 16 * params_q);
  assert_norm (pow2 16 * params_q < pow2 31);
  assert (range (sint_v a - (sint_v u * params_q)) S32);
  let t:(t:int32{range (sint_v a - sint_v t) S32}) = (to_i32 u) *! q in
  //assert (sint_v t = (sint_v u * params_q) @% pow2 32);
  assert (sint_v t = (sint_v u * params_q));
  lemma_mod_mul_distr_l (sint_v u) params_q (pow2 16); 
  assert (sint_v t % pow2 16 = (((sint_v a * params_qinv) % pow2 16) * params_q) % pow2 16);
  lemma_mod_mul_distr_l (sint_v a * params_qinv) params_q (pow2 16); 
  assert (sint_v t % pow2 16 = ((sint_v a * params_qinv) * params_q) % pow2 16);
  paren_mul_right (sint_v a) params_qinv params_q;
  lemma_mod_mul_distr_r (sint_v a) (params_qinv * params_q) (pow2 16);
  assert_norm(params_qinv * params_q % pow2 16 = 1);
  assert (sint_v t % pow2 16 = sint_v a % pow2 16);
  assert (sint_v t % params_q = 0);
  let t2:int32 = a -! t in
 // assert (sint_v t2 = (sint_v a - sint_v t) @% pow2 32); 
  assert(sint_v t2 = sint_v a - sint_v t);
  assert (sint_v t2 % pow2 16 = (sint_v a - sint_v t) % pow2 16);
  lemma_mod_plus_distr_l (sint_v a) (- sint_v t) (pow2 16);
  assert (sint_v t2 % pow2 16 = (sint_v a % pow2 16 - sint_v t) % pow2 16);
  lemma_mod_sub_distr (sint_v a % pow2 16) (sint_v t) (pow2 16);
  assert (sint_v t2 % pow2 16 = 0);
  lemma_mod_plus_distr_l (sint_v a) (- sint_v t) (params_q);
  lemma_mod_sub_distr (sint_v a % params_q) (sint_v t) (params_q);
  assert (sint_v t2 % params_q = sint_v a % params_q);
  let t3 = (t2 >>. size 16) in
  let t4 = to_i16 t3 in
  assert(sint_v t3 = sint_v t2 / (pow2 16));
  assert( ( - pow2 16 * params_q) / pow2 16 < sint_v t3 /\ sint_v t3 < (pow2 16 * params_q) / pow2 16);
  swap_neg_mul (pow2 16) params_q;
  cancel_mul_div params_q (pow2 16);
  cancel_mul_div (-params_q) (pow2 16);
  assert ( - params_q < sint_v t3 /\ sint_v t3 < params_q);
  assert ( (- pow2 31) / pow2 16 <= sint_v t3 /\ sint_v t3 < pow2 31 / pow2 16);
  pow2_minus 31 16;
  assert ( - pow2 15 <= sint_v t3 /\ sint_v t3 < pow2 15);
  assert (sint_v t4 = sint_v t3);
  assert (sint_v t4 * pow2 16 = sint_v t2); 
  assert ( - params_q < sint_v t4 /\ sint_v t4 < params_q);
  assert ((sint_v t4 * pow2 16) % params_q = sint_v a % params_q);
  t4

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

(*val lemma_montgomery_reduce_int32_:
  a:int32
  -> Lemma (requires uint_v a >= - params_q * pow2 (params_logr-1) /\ uint_v a < params_q * pow2 (params_logr-1))
  (ensures (let t = ((to_i32 (to_i16 (a *. i32 params_qinv))) *. i32 params_q) in uint_v t % params_q = 0 /\ uint_v t % pow2 16 = uint_v a % pow2 16  /\ - pow2 16 * params_q < uint_v a - uint_v t /\ uint_v a - uint_v t < pow2 16 * params_q (*/\ uint_v (a-.t) = uint_v a - uint_v t*)))

let lemma_montgomery_reduce_int32_ a =
  let qinv = i32 (params_qinv) in
  let q = i32 (params_q) in
  let u = to_i16 (a *. qinv) in
  assert (uint_v u = ((uint_v a * params_qinv) @% pow2 32) @% pow2 16);
  assert (uint_v u % pow2 16 = ((uint_v a * params_qinv) @% pow2 32) % pow2 16);
  assert (uint_v (a*.qinv) % pow2 32 = (uint_v a * params_qinv) % pow2 32);
  pow2_plus 16 16;
  modulo_modulo_lemma (uint_v (a*.qinv)) (pow2 16) (pow2 16);
  assert (uint_v u % pow2 16 = ((uint_v a * params_qinv) % pow2 32) % pow2 16);
  modulo_modulo_lemma (uint_v a * params_qinv) (pow2 16) (pow2 16);
  assert (uint_v u = ((uint_v a * params_qinv) @% pow2 16));
  let t = (to_i32 u) *. q in
  assert (uint_v t = (uint_v u * params_q) @% pow2 32);
  assert (uint_v t = (uint_v u * params_q));
  lemma_mod_mul_distr_l (uint_v u) params_q (pow2 16); 
  assert (uint_v t % pow2 16 = (((uint_v a * params_qinv) % pow2 16) * params_q) % pow2 16);
  lemma_mod_mul_distr_l (uint_v a * params_qinv) params_q (pow2 16); 
  assert (uint_v t % pow2 16 = ((uint_v a * params_qinv) * params_q) % pow2 16);
  paren_mul_right (uint_v a) params_qinv params_q;
  lemma_mod_mul_distr_r (uint_v a) (params_qinv * params_q) (pow2 16);
  assert_norm(params_qinv * params_q % pow2 16 = 1);
  assert (uint_v t % pow2 16 = uint_v a % pow2 16);
  assert (uint_v t % params_q = 0);
  assert (- pow2 15 * params_q <= uint_v t /\ uint_v t < pow2 15 * params_q);
  assert ( -pow2 15 * params_q < - uint_v t /\ - uint_v t <= pow2 15 * params_q);
  assert ( - 2 * pow2 15 * params_q < uint_v a - uint_v t /\ uint_v a - uint_v t < 2 * pow2 15 * params_q);
  pow2_double_mult 15;
  assert ( - pow2 16 * params_q < uint_v a - uint_v t /\ uint_v a - uint_v t < pow2 16 * params_q);
  assert_norm (pow2 16 * params_q < pow2 31);
  assert ( - pow2 31 <= uint_v a - uint_v t /\ uint_v a - uint_v t <= pow2 31 -1 );
  assert(range (uint_v a - uint_v t) I32);
  //let t':(t:int32{range (uint_v a - uint_v t) I32}) = t in
  let t2:int32 = a -. t in
  assert (uint_v t2 = (uint_v a - uint_v t) @% pow2 32); admit()
  assert(uint_v t2 = uint_v a - uint_v t); admit();
  assert (uint_v t2 % pow2 16 = (uint_v a - uint_v t) % pow2 16);
  lemma_mod_plus_distr_l (uint_v a) (- uint_v t) (pow2 16);
  assert (uint_v t2 % pow2 16 = (uint_v a % pow2 16 - uint_v t) % pow2 16);
  lemma_mod_sub_distr (uint_v a % pow2 16) (uint_v t) (pow2 16);
  assert (uint_v t2 % pow2 16 = 0);
  lemma_mod_plus_distr_l (uint_v a) (- uint_v t) (params_q);
  lemma_mod_sub_distr (uint_v a % params_q) (uint_v t) (params_q);
  assert (uint_v t2 % params_q = uint_v a % params_q)

val lemma_montgomery_reduce_int32:
  a:int32
  -> Lemma (requires uint_v a >= - params_q * pow2 (params_logr-1) /\ uint_v a < params_q * pow2 (params_logr-1)) (ensures (let t = montgomery_reduce_int32 a in uint_v t > - params_q /\ uint_v t < params_q /\ (uint_v t * pow2 params_logr) % params_q = uint_v a % params_q))

#reset-options "--z3rlimit 2000 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let lemma_montgomery_reduce_int32 a =
  let qinv = i32 (params_qinv) in
  let q = i32 (params_q) in
  let u = to_i16 (a *. qinv) in
  let t = (to_i32 u) *. q in
  let t2:int32 = a -. t in
  lemma_montgomery_reduce_int32_ a;
  assert (uint_v t2 % pow2 16 = (uint_v a - uint_v t) % pow2 16);
  lemma_mod_plus_distr_l (uint_v a) (- uint_v t) (pow2 16);
  assert (uint_v t2 % pow2 16 = (uint_v a % pow2 16 - uint_v t) % pow2 16);
  lemma_mod_sub_distr (uint_v a % pow2 16) (uint_v t) (pow2 16);
  assert (uint_v t2 % pow2 16 = 0);
  lemma_mod_plus_distr_l (uint_v a) (- uint_v t) (params_q);
  lemma_mod_sub_distr (uint_v a % params_q) (uint_v t) (params_q);
  assert (uint_v t2 % params_q = uint_v a % params_q);
  let t3 = (t2 >>. size 16) in
  let t4 = to_i16 t3 in
  assert(uint_v t3 = uint_v t2 / (pow2 16));
  assert( ( - pow2 16 * params_q) / pow2 16 < uint_v t3 /\ uint_v t3 < (pow2 16 * params_q) / pow2 16);
  swap_neg_mul (pow2 16) params_q;
  cancel_mul_div params_q (pow2 16);
  cancel_mul_div (-params_q) (pow2 16);
  assert ( - params_q < uint_v t3 /\ uint_v t3 < params_q); admit();
  assert_norm (params_q < pow2 16); admit();
  assert ( -pow2 15 <= uint_v t3 /\ uint_v t3 < pow2 15); admit();
  assert (uint_v t4 = uint_v t3);
  assert (uint_v t4 * pow2 16 = uint_v t2); admit()
*)
(*  
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
  (*assert( a + ((( a * params_qinv) % pow2 params_logr) * par62209ams_q ) % pow2 params_logr ==  a + ( a * params_qinv * params_q) % pow2 params_logr);
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
*)

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


val barrett_reduce:
  a:nat{a<pow2 15}
  -> Tot (res:nat{res = a % params_q})

let barrett_reduce a =
  let v = ((pow2 26) / params_q) + 1 in
  let t = ((v*a) / (pow2 26)) * params_q in
  assert ((v*a) - pow2 26 <= pow2 26 * ((v*a)/pow2 26) /\ pow2 26 * ((v*a)/pow2 26) <= v*a);
  assert(params_q * ((v*a) - pow2 26) <= pow2 26 * t /\ pow2 26 * t <= params_q * (v*a));
  paren_mul_right params_q v a;
  paren_mul_left params_q v a;
  distributivity_add_right params_q ((pow2 26) / params_q) 1;
  assert(params_q * v = pow2 26 - ((pow2 26) % params_q) + params_q);
  assert(params_q * (v*a) = (pow2 26 - ((pow2 26) % params_q) + params_q) * a);
  distributivity_add_left (pow2 26 - ((pow2 26) % params_q)) params_q a;
  lemma_mul_sub_distr a (pow2 26) ((pow2 26) % params_q);
  assert(params_q * (v*a) = (a * pow2 26 - a * (pow2 26 % params_q) + a * params_q));
  assert(params_q * (v*a) = (a * pow2 26 + a * params_q - a * (pow2 26 % params_q)));
  lemma_mul_sub_distr a params_q (pow2 26 % params_q);
  assert(t * pow2 26 <= (a * pow2 26 + (pow2 16) * (params_q - (pow2 26 % params_q))));
  lemma_div_le (t * pow2 26) (a * pow2 26 + (pow2 16) * (params_q - (pow2 26 % params_q))) (pow2 26);
  cancel_mul_div t (pow2 26);
  lemma_div_plus (pow2 16 * (params_q - (pow2 26 % params_q))) a (pow2 26);
  assert_norm((pow2 16 * (params_q - (pow2 26 % params_q))) / pow2 26 = 0);
  assert(t <= a);
  assert(params_q * v > pow2 26);
  lemma_mul_sub_distr params_q (v*a) (pow2 26);
  lemma_mult_le_right a (pow2 26) (params_q * v);
  assert(a * pow2 26 - params_q * pow2 26 <= params_q * ((v*a) - pow2 26));
  lemma_mul_sub_distr (pow2 26) a params_q;
  assert((a - params_q) * pow2 26 < pow2 26 * t);
  if (a-params_q >= 0) then begin
    lemma_div_le ((a-params_q) * pow2 26) (t* pow2 26) (pow2 26);
    cancel_mul_div (a-params_q) (pow2 26);
    cancel_mul_div t (pow2 26);
    assert(a - params_q < t) end
  else
    assert(a - params_q < t);
  assert(a-params_q < t);
  assert(-a <= -t /\ -t < params_q -a);
  assert(0 <= a - t /\ a - t < params_q);
  cancel_mul_mod ((v*a) / (pow2 26)) params_q;
  assert(t % params_q = 0);
  lemma_mod_sub_distr a t params_q;
  a - t


#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lemma_barrett_int16:
  a:int16
  -> Tot (t:int16{uint_v t % params_q = uint_v a % params_q /\ 0 <= uint_v t /\ uint_v t <= params_q})

let lemma_barrett_int16 a =
  let q = i32 params_q in
  let v = i32 ((pow2 26)/params_q + 1) in
  let t = v *! (to_i32 a) in
  let t2 = t >>. size 26 in
  assert(uint_v t2 = uint_v t / pow2 26);
  assert(uint_v t2 = (uint_v v * uint_v a) / pow2 26);
  assert((uint_v v * uint_v a) - pow2 26 < pow2 26 * uint_v t2 /\ pow2 26 * uint_v t2 <= (uint_v v * uint_v a));
  let t3 = t2 *! q in
  paren_mul_right (pow2 26) (uint_v t2) (params_q);
  assert(((uint_v v * uint_v a) - pow2 26) * params_q < pow2 26 * uint_v t3 /\ pow2 26 * uint_v t3 <= (uint_v v * uint_v a) * params_q);
  distributivity_sub_left (uint_v v * uint_v a) (pow2 26) (params_q);
  swap_mul (uint_v v) (uint_v a);
  paren_mul_right (uint_v a) (uint_v v) params_q;
  distributivity_add_left (pow2 26 / params_q) 1 params_q;
  assert (uint_v v * params_q = pow2 26 - ((pow2 26) % params_q) + params_q);
  assert (uint_v v * params_q = pow2 26 + (params_q - ((pow2 26) % params_q)));
  distributivity_add_right (uint_v a) (pow2 26) (params_q - ((pow2 26) % params_q));
  assert ((uint_v v * uint_v a) * params_q <= uint_v a * pow2 26 + (pow2 15) * (params_q - ((pow2 26) % params_q)));
  assert ((uint_v a * uint_v v) * params_q >= uint_v a * pow2 26 - (pow2 15) * (params_q - ((pow2 26) % params_q)));
  distributivity_sub_left (uint_v a) params_q (pow2 26);
  assert ((uint_v a - params_q) * pow2 26 - (pow2 15) * (params_q - ((pow2 26) % params_q)) < pow2 26 * uint_v t3);
  lemma_div_plus ( - (pow2 15) * (params_q - ((pow2 26) % params_q))) (uint_v a - params_q) (pow2 26);
  assert_norm ( ( - (pow2 15) * (params_q - ((pow2 26) % params_q))) / pow2 26 = -1);
  assert (((uint_v a - params_q) * pow2 26 - (pow2 15) * (params_q - ((pow2 26) % params_q))) / pow2 26 = (uint_v a - params_q - 1));
  assert ((uint_v a - params_q) <= uint_v t3);

  lemma_div_plus ((pow2 15) * (params_q - ((pow2 26) % params_q))) (uint_v a - params_q) (pow2 26);
  assert_norm (((pow2 15) * (params_q - ((pow2 26) % params_q))) / pow2 26 = 0);
  assert(uint_v t3 <= uint_v a);
  //assert (uint_v a * (pow2 26 - ((pow2 26) % params_q) + params_q) - pow2 26 * params_q <= pow2 26 * uint_v t3
  let t4 = to_i16 (to_i32 a -! t3) in
  assert (0 <= uint_v t4 /\ uint_v t4 <= params_q);
  lemma_mod_plus (uint_v a) (-uint_v t2) params_q;
  t4

(*
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
*)

val csubq_int16:
  a:int16{uint_v a - params_q >= minint S16}
  -> t:int16{if (uint_v a >= params_q) then uint_v t = uint_v a - params_q else uint_v t = uint_v a}

let csubq_int16 a =
  let a2 = a -! (i16 params_q) in
  let a3 = (a2 >>. size 15) &. (i16 params_q) in
  if (uint_v a >= params_q) then begin
    assert(uint_v a2 >= 0);
    assert (uint_v (a2 >>. size 15) = 0)
  end
  else begin
    assert(uint_v a2 < 0);
    assert(uint_v (a2 >>. size 15) = -1)
  end;
  logand_lemma (a2 >>. size 15) (i16 params_q);
  a2 +! a3
