module Impl.Kyber2.Reduce

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


#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

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
  //admit();
  let t3 = (t2 >>. size 16) in
  let t4 = to_i16 t3 in
  shift_right_lemma t2 (size 16);
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


#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val barrett_reduce_int16:
  a:int16
  -> Tot (t:int16{sint_v t % params_q = sint_v a % params_q /\ 0 <= sint_v t /\ sint_v t <= params_q})

let barrett_reduce_int16 a =
  let q = i32 params_q in
  let v = i32 ((pow2 26)/params_q + 1) in
  let t = v *! (to_i32 a) in
  let t2 = t >>. size 26 in
  assert(sint_v t2 = sint_v t / pow2 26);
  assert(sint_v t2 = (sint_v v * sint_v a) / pow2 26);
  assert((sint_v v * sint_v a) - pow2 26 < pow2 26 * sint_v t2 /\ pow2 26 * sint_v t2 <= (sint_v v * sint_v a));
  let t3 = t2 *! q in
  paren_mul_right (pow2 26) (sint_v t2) (params_q);
  assert(((sint_v v * sint_v a) - pow2 26) * params_q < pow2 26 * sint_v t3 /\ pow2 26 * sint_v t3 <= (sint_v v * sint_v a) * params_q);
  distributivity_sub_left (sint_v v * sint_v a) (pow2 26) (params_q);
  swap_mul (sint_v v) (sint_v a);
  paren_mul_right (sint_v a) (sint_v v) params_q;
  distributivity_add_left (pow2 26 / params_q) 1 params_q;
  assert (sint_v v * params_q = pow2 26 - ((pow2 26) % params_q) + params_q);
  assert (sint_v v * params_q = pow2 26 + (params_q - ((pow2 26) % params_q)));
  distributivity_add_right (sint_v a) (pow2 26) (params_q - ((pow2 26) % params_q));
  assert ((sint_v v * sint_v a) * params_q <= sint_v a * pow2 26 + (pow2 15) * (params_q - ((pow2 26) % params_q)));
  assert ((sint_v a * sint_v v) * params_q >= sint_v a * pow2 26 - (pow2 15) * (params_q - ((pow2 26) % params_q)));
  distributivity_sub_left (sint_v a) params_q (pow2 26);
  assert ((sint_v a - params_q) * pow2 26 - (pow2 15) * (params_q - ((pow2 26) % params_q)) < pow2 26 * sint_v t3);
  lemma_div_plus ( - (pow2 15) * (params_q - ((pow2 26) % params_q))) (sint_v a - params_q) (pow2 26);
  assert_norm ( ( - (pow2 15) * (params_q - ((pow2 26) % params_q))) / pow2 26 = -1);
  assert (((sint_v a - params_q) * pow2 26 - (pow2 15) * (params_q - ((pow2 26) % params_q))) / pow2 26 = (sint_v a - params_q - 1));
  assert ((sint_v a - params_q) <= sint_v t3);
  lemma_div_plus ((pow2 15) * (params_q - ((pow2 26) % params_q))) (sint_v a) (pow2 26);
  assert_norm (((pow2 15) * (params_q - ((pow2 26) % params_q))) / pow2 26 = 0);
  assert(sint_v t3 <= sint_v a);
  //assert (sint_v a * (pow2 26 - ((pow2 26) % params_q) + params_q) - pow2 26 * params_q <= pow2 26 * sint_v t3
  let t4 = to_i16 (to_i32 a -! t3) in
  assert (0 <= sint_v t4 /\ sint_v t4 <= params_q);
  lemma_mod_plus (sint_v a) (-sint_v t2) params_q;
  t4


val csubq_int16:
  a:int16{sint_v a - params_q >= minint S16}
  -> t:int16{if (sint_v a >= params_q) then sint_v t = sint_v a - params_q else sint_v t = sint_v a}

let csubq_int16 a =
  let a2 = a -! (i16 params_q) in
  let a3 = (a2 >>. size 15) &. (i16 params_q) in
  if (sint_v a >= params_q) then begin
    assert(sint_v a2 >= 0);
    assert (sint_v (a2 >>. size 15) = 0)
  end
  else begin
    assert(sint_v a2 < 0);
    assert(sint_v (a2 >>. size 15) = -1)
  end;
  logand_lemma (a2 >>. size 15) (i16 params_q);
  a2 +! a3

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

val division_by_q_int32_:
  a:int32
  -> d:int32{sint_v d <= sint_v a / params_q /\ sint_v d >= sint_v a / params_q - 1}

let division_by_q_int32_ a =
  let q = i64 params_q in
  pow2_le_compat 63 43;
  assert (pow2 43/params_q < pow2 43);
  let v = i64 ((pow2 43)/params_q + 1) in
  assert_norm (sint_v v < pow2 32 /\ sint_v v >= 0);
  assert_norm (range (sint_v v * sint_v (to_i64 a)) S64);
  let t = v *! (to_i64 a) in
  let t2:int32 = to_i32 (t >>. size 43) in
  assert_norm (sint_v t / pow2 43 <= pow2 63 / pow2 43);
  assert_norm (- pow2 63 / pow2 43 <= sint_v t / pow2 43);
  pow2_lt_compat 63 43;
  pow2_lt_compat 31 20;
  assert_norm( range (sint_v t / pow2 43) S32);
  assert(sint_v t2 = (sint_v t / pow2 43));
  assert(sint_v t2 = (sint_v v * sint_v a) / pow2 43);
  assert((sint_v v * sint_v a) - pow2 43 < pow2 43 * sint_v t2 /\ pow2 43 * sint_v t2 <= (sint_v v * sint_v a));
  let t3 = (to_i64 t2) *! q in
  paren_mul_right (pow2 43) (sint_v t2) (params_q);
  assert(((sint_v v * sint_v a) - pow2 43) * params_q < pow2 43 * sint_v t3 /\ pow2 43 * sint_v t3 <= (sint_v v * sint_v a) * params_q);
  distributivity_sub_left (sint_v v * sint_v a) (pow2 43) (params_q);
  swap_mul (sint_v v) (sint_v a);
  paren_mul_right (sint_v a) (sint_v v) params_q;
  distributivity_add_left (pow2 43 / params_q) 1 params_q;
  assert (sint_v v * params_q = pow2 43 - ((pow2 43) % params_q) + params_q);
  assert (sint_v v * params_q = pow2 43 + (params_q - ((pow2 43) % params_q)));
  distributivity_add_right (sint_v a) (pow2 43) (params_q - ((pow2 43) % params_q));
  assert_norm ((sint_v v * sint_v a) * params_q <= sint_v a * pow2 43 + (pow2 31) * (params_q - ((pow2 43) % params_q)));
  assert_norm ((sint_v a * sint_v v) * params_q >= sint_v a * pow2 43 - (pow2 31) * (params_q - ((pow2 43) % params_q)));
  assert_norm (0 <= (pow2 31) * (params_q - ((pow2 43) % params_q)) /\ (pow2 31) * (params_q - ((pow2 43) % params_q)) < pow2 43);
  assert(sint_v t3 * pow2 43 <= sint_v a * pow2 43 + (pow2 31) * (params_q - ((pow2 43) % params_q)));
  assert (sint_v a * pow2 43 + ((pow2 31) * (params_q - ((pow2 43) % params_q))) < sint_v a * pow2 43 + pow2 43); 
  distributivity_add_left (sint_v a) 1 (pow2 43);
  assert (sint_v t3 * pow2 43 < (sint_v a + 1) * pow2 43);
  if (sint_v t3 >= sint_v a + 1) then begin
    lemma_mult_le_right (pow2 43) (sint_v a + 1) (sint_v t3);
    assert(false) end;
  assert (sint_v t3 <= sint_v a);

  distributivity_sub_left (sint_v a) params_q (pow2 43);
  assert ((sint_v a - params_q) * pow2 43 - (pow2 31) * (params_q - ((pow2 43) % params_q)) < pow2 43 * sint_v t3);
  assert ((sint_v t3 + params_q - sint_v a) * pow2 43 + (pow2 31) * (params_q - ((pow2 43)% params_q)) > 0);
  (*lemma_div_plus ((pow2 31) * (params_q - ((pow2 43) % params_q))) (sint_v t3 + params_q - sint_v a) (pow2 43);
  assert_norm ( ((pow2 31) * (params_q - ((pow2 43) % params_q))) / pow2 43 = 0);
  assert (((sint_v t3 + params_q - sint_v a) * pow2 43 + (pow2 31) * (params_q - ((pow2 43) % params_q))) / pow2 43 = (sint_v t3 + params_q - sint_v a));
  assert_norm (0 <= (pow2 31) * (params_q - ((pow2 43) % params_q)) /\ (pow2 31) * (params_q - ((pow2 43) % params_q)) < pow2 43);*)
  if (sint_v t3 + params_q - sint_v a < 0) then begin
    lemma_mult_le_right (pow2 43) (sint_v t3 + params_q - sint_v a) (-1);
    assert ((sint_v t3 + params_q - sint_v a) * pow2 43 <= - pow2 43);
    assert_norm ((sint_v t3 + params_q - sint_v a) * pow2 43 + (pow2 31) * (params_q - ((pow2 43) % params_q)) <= 0);
    assert(false) end;
  assert((sint_v a - params_q) <= sint_v t3);

  assert( (sint_v a - params_q < (sint_v a / params_q) * params_q) /\ (sint_v a / params_q) * params_q <= sint_v a);
  assert (sint_v a < (sint_v a / params_q +1 ) * params_q);
  assert ((sint_v a / params_q -1) * params_q <= sint_v a - params_q);
  if( sint_v t2 > sint_v a / params_q) then
    begin
      lemma_mult_le_right (params_q) (sint_v a / params_q + 1) (sint_v t2);
      assert ((sint_v a / params_q + 1) * params_q <= sint_v t3);
      assert (sint_v a < sint_v t3);
      assert (false)
    end;

  if (sint_v t2 < sint_v a / params_q - 1) then
    begin
      lemma_mult_le_right (params_q) (sint_v t2) (sint_v a / params_q - 2);
      assert (sint_v t3 < (sint_v a / params_q - 1) * params_q);
      assert (sint_v t3 < sint_v a - params_q);
      assert (false)
    end;

  assert (sint_v t2 <= sint_v a / params_q /\ sint_v t2 >= sint_v a / params_q - 1);
  t2

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

val division_by_q_int32_cadd1_:
  a:int32
  -> b:int32{sint_v b <= sint_v a / params_q /\ sint_v b >= sint_v a / params_q - 1}
  -> c:int32{sint_v c = sint_v a / params_q}

let division_by_q_int32_cadd1_ a b =
  let q = i64 params_q in
  let bq = to_i64 b *! q in
  assert(sint_v bq = sint_v b * params_q);
  assert (sint_v bq <= sint_v a /\ sint_v bq > sint_v a - 2*params_q);
  let a2 = to_i32 (to_i64 a -! bq) in
  assert_norm (range (sint_v a - sint_v bq) S32);
  assert (sint_v a2 = sint_v a - sint_v bq);
  lemma_div_plus (sint_v a) (sint_v b) (params_q);
  assert (sint_v a2 % params_q = sint_v a % params_q);
  assert (sint_v a2 >= 0 /\ sint_v a2 < 2 * params_q);
  assert (sint_v a2 < params_q <==> sint_v a2 = sint_v a % params_q);
  assert (sint_v a2 < params_q <==> sint_v bq = (sint_v a / params_q) * params_q);
  let cst = a2 -! i32 params_q in
  assert (sint_v cst = sint_v a2 - params_q);
  assert (sint_v cst < 0 <==> sint_v b = (sint_v a / params_q));
  let mask = cst >>. size 31 in
  assert_norm (sint_v b = (sint_v a / params_q) ==> sint_v mask = -1);
  assert_norm (sint_v b = (sint_v a / params_q) - 1 ==> sint_v mask = 0);
  b +! i32 1 +! mask

val division_by_q_int32:
  a:int32
  -> b:int32{sint_v b = sint_v a / params_q}

let division_by_q_int32 a =
  division_by_q_int32_cadd1_ a (division_by_q_int32_ a)
