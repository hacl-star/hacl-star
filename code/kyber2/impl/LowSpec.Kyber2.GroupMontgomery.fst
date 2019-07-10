module LowSpec.Kyber2.GroupMontgomery

open Lib.Arithmetic.Group
open Lib.IntTypes
open FStar.Math.Lemmas
open Lib.ModularArithmetic.Lemmas
open FStar.Mul
open Spec.Kyber2.Params
open Spec.Kyber2.Reduce

module Group = Spec.Kyber2.Group

inline_for_extraction noextract
type montgomery (x:Group.t) = y:int16{ sint_v y <= params_q /\ sint_v y >= - params_q /\ sint_v y % params_q = (Group.v x * pow2 params_logr) % params_q}

inline_for_extraction
let zero_m : montgomery (Group.zero_t) = Group.zero_t

inline_for_extraction
let one_m : montgomery (Group.one_t) = Group.mk_t params_mont

let from_t (x:Group.t) : montgomery x =
  let mr = montgomery_reduce_int32 ((to_i32 x) *! (i32 params_mont2)) in
  lemma_mod_mul_distr_l (sint_v mr * pow2 params_logr) params_rinv params_q;
  paren_mul_right (sint_v mr) (pow2 params_logr) params_rinv;
  lemma_mod_mul_distr_r (sint_v mr) ((pow2 params_logr) * params_rinv) params_q;
  assert_norm (((pow2 params_logr) * params_rinv) % params_q = 1);
  lemma_mod_mul_distr_l (Group.v x * params_mont2) params_rinv params_q;
  paren_mul_right (Group.v x) params_mont2 params_rinv;
  lemma_mod_mul_distr_r (Group.v x) (params_mont2 * params_rinv) params_q;
  assert_norm ((params_mont2 * params_rinv) % params_q = pow2 params_logr % params_q);
  lemma_mod_mul_distr_r (Group.v x) (pow2 params_logr) params_q;
  mr

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let to_t #x' (x:montgomery x') : Pure Group.t (requires True) (ensures fun r -> r == x') =
  let mr = montgomery_reduce_int32 (to_i32 x) in
  assert ((sint_v mr * pow2 params_logr) % params_q = sint_v x % params_q);
  lemma_mod_mul_distr_l (sint_v mr * pow2 params_logr) params_rinv params_q;
  paren_mul_right (sint_v mr) (pow2 params_logr) params_rinv;
  lemma_mod_mul_distr_r (sint_v mr) ((pow2 params_logr) * params_rinv) params_q;
  assert_norm (((pow2 params_logr) * params_rinv) % params_q = 1);
  assert (sint_v mr % params_q = ((sint_v x % params_q) * params_rinv) % params_q);
  assert(sint_v mr % params_q = (((Group.v x' * pow2 params_logr) % params_q) * params_rinv) % params_q);
  lemma_mod_mul_distr_l (Group.v x' * (pow2 params_logr)) params_rinv params_q;
  paren_mul_right (Group.v x') (pow2 params_logr) params_rinv;
  lemma_mod_mul_distr_r (Group.v x') ((pow2 params_logr) * params_rinv) params_q;
  assert (sint_v mr % params_q = Group.v x' % params_q);
  let r = csubq_int16 (mr +! i16 params_q) in
  lemma_mod_plus (sint_v mr) 1 params_q;
  r

let to_t_lemma #x' (x:montgomery x') : Lemma (to_t x == to_t (from_t x')) = ()
#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let plus_m #x' #y' (x:montgomery x') (y:montgomery y') : montgomery (Group.plus_t x' y') =
  let br = barrett_reduce_int16 (x +! y) in
  assert (sint_v br % params_q = (sint_v x + sint_v y) % params_q);
  lemma_mod_plus_distr_l (sint_v x) (sint_v y) params_q;
  lemma_mod_plus_distr_r ((sint_v x) % params_q) (sint_v y) (params_q);
  lemma_mod_plus_distr_l (sint_v x) (sint_v y) params_q;
  assert (sint_v br % params_q = (((Group.v x' * pow2 params_logr) % params_q) + ((Group.v y' * pow2 params_logr) % params_q)) % params_q);
  lemma_mod_plus_distr_r ((Group.v x' * pow2 params_logr) % params_q) (Group.v y' * pow2 params_logr) (params_q);
  lemma_mod_plus_distr_l (Group.v x' * pow2 params_logr) (Group.v y' * pow2 params_logr) (params_q);
  distributivity_add_left (Group.v x') (Group.v y') (pow2 params_logr);
  lemma_mod_mul_distr_l (Group.v x' + Group.v y') (pow2 params_logr) params_q;
  Group.plus_lemma_t x' y';
  br


#reset-options "--z3rlimit 1000 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let mul_m #x' #y' (x:montgomery x') (y:montgomery y') : montgomery (Group.mul_t x' y') =
  assert_norm (range (sint_v x) S32);
  assert_norm (range (sint_v y) S32);
  assert_norm (sint_v x * sint_v y <= params_q * params_q);
  assert_norm ( - params_q * params_q <= sint_v x * sint_v y);
  assert_norm ( params_q * params_q < params_q * pow2 (params_logr-1));
  assert_norm ( - params_q * pow2 (params_logr - 1) <= - params_q * params_q);
  assert_norm ( params_q * params_q <= maxint S32);
  assert_norm ( minint S32 <= - params_q * params_q);
  assert_norm (range (sint_v x * sint_v y) S32);
  let mr = montgomery_reduce_int32 ((to_i32 x) *! (to_i32 y)) in
  assert((sint_v mr * pow2 params_logr) % params_q = (sint_v x * sint_v y) % params_q);
  lemma_mod_mul_distr_l (sint_v mr * pow2 params_logr) params_rinv params_q;
  paren_mul_right (sint_v mr) (pow2 params_logr) params_rinv;
  lemma_mod_mul_distr_r (sint_v mr) ((pow2 params_logr) * params_rinv) params_q;
  assert_norm (((pow2 params_logr) * params_rinv) % params_q = 1);
  assert(sint_v mr % params_q = (((sint_v x * sint_v y) % params_q) * params_rinv) % params_q);
  lemma_mod_mul_distr_l (sint_v x * sint_v y) params_rinv params_q;
  assert(sint_v mr % params_q = ((sint_v x * sint_v y)* params_rinv) % params_q);

  paren_mul_right (sint_v x) (sint_v y) params_rinv;
  lemma_mod_mul_distr_r (sint_v x) (sint_v y * params_rinv) (params_q);
  assert(sint_v mr % params_q = ( sint_v x * ((sint_v y * params_rinv) % params_q)) % params_q);

  lemma_mod_mul_distr_l (sint_v y) params_rinv params_q;
  lemma_mod_mul_distr_l (Group.v y' * pow2 params_logr) params_rinv params_q;
  assert(sint_v mr % params_q = ( sint_v x * (((Group.v y' * pow2 params_logr) * params_rinv) % params_q)) % params_q);
  paren_mul_right (Group.v y') (pow2 params_logr) params_rinv;
  lemma_mod_mul_distr_r (Group.v y') ((pow2 params_logr) * params_rinv) params_q;
  lemma_mod_mul_distr_r (sint_v x) (Group.v y') params_q;
  assert(sint_v mr % params_q = (sint_v x * Group.v y') % params_q);

  lemma_mod_mul_distr_l (sint_v x) (Group.v y') params_q;
  lemma_mod_mul_distr_l ((Group.v x') * pow2 params_logr) (Group.v y') params_q;
  paren_mul_right (Group.v x') (pow2 params_logr) (Group.v y');
  swap_mul (pow2 params_logr) (Group.v y');
  paren_mul_right (Group.v x') (Group.v y') (pow2 params_logr);
  lemma_mod_mul_distr_l ((Group.v x') * (Group.v y')) (pow2 params_logr) params_q;
  Group.mul_lemma_t x' y';
  mr

let opp_m #x' (x:montgomery x') : montgomery (sym #Group.t #Group.group_t x') =
  assert_norm (range (-sint_v x) S16);
  Group.opp_lemma_t x';
  lemma_mod_sub_distr 0 (sint_v x) params_q;
  lemma_mod_sub_distr 0 (Group.v x' * pow2 params_logr) params_q;
  lemma_mod_mul_distr_l (- Group.v x') (pow2 params_logr) params_q;
  zero_m -! x

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let rec exp_m #x' (x:montgomery x') (n:size_t) : Tot (montgomery (repeat_op #Group.t #Group.monoid_mul_t x' (v n))) (decreases (v n)) =
  if (n =. (size 0)) then one_m
  else let b = exp_m x (n /. (size 2)) in
  let b2 = mul_m b b in
  if (n %. (size 2) =. (size 0)) then b2 else mul_m x b2
