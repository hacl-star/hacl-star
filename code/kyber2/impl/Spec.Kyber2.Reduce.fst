module Spec.Kyber2.Reduce

open Lib.IntTypes

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Kyber2.Params
open FStar.Math.Lemmas
//open Spec.Kyber2.Lemmas
//open Spec.Powtwo.Lemmas
//open Lib.ModularArithmetic
//open Lib.ModularArithmetic.Lemmas

//module Seq = Lib.Sequence
//module Loops = Lib.LoopCombinators



#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

inline_for_extraction
val int64_to_int16: a:int64 -> Tot (b:int16{sint_v b == sint_v a @%. S16})

inline_for_extraction
let mod_mask (#t:inttype) (#l:secrecy_level) (m:shiftval t{uint_v m + 1<bits t}) : int_t t l =
  assert_norm(range 1 t);
  pow2_lt_compat (bits t - 1) (uint_v m);
  pow2_le_compat (uint_v m) 0;
  assert(range (pow2 (uint_v m)) t);
  assert(range (pow2 (uint_v m) - 1) t);
  shift_left_lemma (mk_int #t #l 1) m;
  ((mk_int 1) <<. m) -! (mk_int 1)

private
val mod_mask_value: #t:inttype -> #l:secrecy_level -> m:shiftval t{uint_v m + 1 < bits t} ->
  Lemma (Lib.IntTypes.v (mod_mask #t #l m) == pow2 (v m) - 1)

let mod_mask_value #t #l m =
  assert_norm(range 1 t);
  pow2_lt_compat (bits t - 1) (uint_v m);
  pow2_le_compat (uint_v m) 0;
  assert(range (pow2 (uint_v m)) t);
  assert(range (pow2 (uint_v m) - 1) t);
  shift_left_lemma (mk_int #t #l 1) m;
  sub_lemma (mk_int #t #l 1 <<. m) (mk_int #t #l 1)

val mod_mask_lemma: #t:inttype -> #l:secrecy_level -> a:int_t t l -> m:shiftval t{uint_v m +1 < bits t}
  -> Lemma (Lib.IntTypes.v (a `logand` mod_mask m) == Lib.IntTypes.v a % pow2 (v m))
  [SMTPat (a `logand` mod_mask #t m)]

#set-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"

let mod_mask_lemma #t #l a m =
  mod_mask_value #t #l m;
  logand_spec #t #l a (mod_mask m);
  if (unsigned t || (Lib.IntTypes.v a >= 0)) then
    if(v m = 0) then
      UInt.logand_lemma_1 #(bits t) (Lib.IntTypes.v a)
    else
      UInt.logand_mask #(bits t) (Lib.IntTypes.v a) (v m)
  else
    begin
    let a1 = Lib.IntTypes.v a in
    let a2 = FStar.Int.to_uint a1 in
    assert (a2 = a1 + pow2 (bits t));
    let s = FStar.Int.logand #(bits t) a1 (pow2 (v m) - 1) in
    let u = FStar.UInt.logand #(bits t) a2 (pow2 (v m) -1) in
    if(v m = 0) then
      UInt.logand_lemma_1 #(bits t) a2
    else
      UInt.logand_mask #(bits t) a2 (v m);
    pow2_plus ((bits t) - (v m)) (v m);
    pow2_le_compat (bits t -1) (v m);
    lemma_mod_plus (Lib.IntTypes.v a) (pow2 ((bits t) - (v m))) (pow2 (v m))
    end

inline_for_extraction
let csub64_to_16 (a:int64{range (sint_v a) U16}) : Tot (b:int64{sint_v b == sint_v a @%. S16}) =
  let pow16 = (mk_int #S64 #SEC 1) <<. (size 16) in
  shift_left_lemma (mk_int #S64 #SEC 1) (size 16);
  let pow15 = (mk_int #S64 #SEC 1) <<. (size 15) in
  shift_left_lemma (mk_int #S64 #SEC 1) (size 15);
  let a2 = a -! pow15 in
  let mask = a2 >>. size 63 in
  shift_right_lemma a2 (size 63);
  assert_norm (Lib.IntTypes.v a2 < 0 ==> Lib.IntTypes.v mask = -1 /\ Lib.IntTypes.v a2 >= 0 ==> v mask = 0);
  let a3 = a -! pow16 in
  logand_lemma mask pow16;
  a3 +! (mask &. pow16)

let int64_to_int16 a =
  let mask = mod_mask #S64 #SEC (size 16) in
  mod_mask_lemma a (size 16);
  let a2 = a &. mask in
  to_i16 (csub64_to_16 a2)

let lemma_div_le (a:int) (b:int) (d:pos) : Lemma
  (requires (a <= b))
  (ensures  (a / d <= b / d))
  = lemma_div_mod a d;
    lemma_div_mod b d;
    cut (d * (a / d) + a % d <= d * (b / d) + b % d);
    cut (d * (a / d) - d * (b / d) <= b % d - a % d);
    distributivity_sub_right d (a/d) (b/d);
    cut (b % d < d /\ a % d < d);
    cut (d * (a/d - b/d) <= d)

inline_for_extraction
val montgomery_reduce_int32:
  a:int32
  -> Pure int16
  (requires (sint_v a >= - params_q * pow2 (params_logr-1) /\ sint_v a < params_q * pow2 (params_logr-1)))
  (ensures fun t -> sint_v t > - params_q /\ sint_v t < params_q /\ (sint_v t * pow2 params_logr) % params_q = sint_v a % params_q)
(*
let lemma_montgomery1 (a:int32) (u:int16) : Lemma (requires ((sint_v u * params_q) % pow2 (params_logr) = sint_v a % pow2 (params_logr) /\ sint_v a >= - params_q * pow2 (params_logr-1) /\ sint_v a < params_q * pow2 (params_logr-1))) (ensures range (sint_v u * params_q) S32 /\ range (sint_v a - (sint_v u * params_q)) S32 /\ (sint_v a - (sint_v u * params_q)) % pow2 (params_logr) = 0) =
  swap_mul params_q (pow2 (params_logr-1));
  swap_neg_mul params_q (pow2 (params_logr-1));
  assert( (- (pow2 15 - 1)) * params_q <= - sint_v u * params_q /\ - sint_v u * params_q <= pow2 15 * params_q);
  pow2_double_mult 15;
  distributivity_add_left (- pow2 15) (-(pow2 15 - 1)) params_q;
  distributivity_add_left (pow2 15 - 1) (pow2 15) params_q;
  assert_norm ( - pow2 15 + (- (pow2 15 - 1)) = - (pow2 16 - 1));
  assert_norm (pow2 15 - 1 + pow2 15 = pow2 16 - 1);
  assert ( - pow2 15 * params_q - (pow2 15 - 1) * params_q <= sint_v a - (sint_v u * params_q));
  assert ( - (pow2 16 - 1) * params_q <= sint_v a - (sint_v u * params_q) /\ sint_v a - (sint_v u * params_q) < (pow2 16) * params_q);
  assert_norm ((pow2 16-1) * params_q < pow2 31);
  lemma_mod_plus_distr_l (sint_v a) (- (sint_v u * params_q)) (pow2 16);
  lemma_mod_sub_distr (sint_v a % pow2 16) (sint_v u * params_q) (pow2 16)*)

let lemma_montgomery2 (a:int32) : Lemma (requires (sint_v a % pow2 16 = 0 /\ sint_v a / pow2 16 <= params_q /\ sint_v a < params_q * pow2 16)) (ensures sint_v a / pow2 16 < params_q) =
  euclidean_division_definition (sint_v a) (pow2 16);
  if (sint_v a / pow2 16 = params_q) then assert(false)

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let montgomery_reduce_int32 a =
  assert_norm (range params_qinv S64);
  assert_norm (range params_q S32);
  let qinv = i64 (params_qinv) in
  let q = i32 (params_q) in
  mul_lemma (to_i64 a) qinv;
  let u = to_i32 (int64_to_int16 ((to_i64 a) *! qinv)) in
  assert (sint_v u = (sint_v a * params_qinv) @%. S16);
  lemma_mult_le_right params_q (sint_v u) (pow2 15 -1);
  lemma_mult_le_right params_q ( - pow2 15) (sint_v u);
  assert_norm (params_q < pow2 12);
  lemma_mult_lt_left (pow2 15) params_q (pow2 12);
  pow2_plus 15 12;
  pow2_lt_compat 31 27;
  assert(pow2 15 * params_q < pow2 31);
  assert(range (sint_v u * params_q) S32);
  assert( (- (pow2 15 - 1)) * params_q <= - sint_v u * params_q /\ - sint_v u * params_q <= pow2 15 * params_q);
  pow2_double_mult 15;
  distributivity_add_left (- pow2 15) (-(pow2 15 - 1)) params_q;
  distributivity_add_left (pow2 15 - 1) (pow2 15) params_q;
  assert_norm ( - pow2 15 + (- (pow2 15 - 1)) = - (pow2 16 - 1));
  assert_norm (pow2 15 - 1 + pow2 15 = pow2 16 - 1);
  assert ( - (pow2 16 - 1) * params_q <= sint_v a - (sint_v u * params_q) /\ sint_v a - (sint_v u * params_q) < (pow2 16) * params_q);
  assert_norm ((pow2 16-1) * params_q < pow2 31);
  assert (range (sint_v a - (sint_v u * params_q)) S32);
  mul_lemma u q;
  let t:(t:int32{range (sint_v a - sint_v t) S32}) = u *! q in
  assert (sint_v t = (sint_v u * params_q));
  lemma_mod_mul_distr_l (sint_v u) params_q (pow2 16);
  assert_norm (sint_v u % pow2 16 = (sint_v a * params_qinv) % pow2 16);
  assert (sint_v t % pow2 16 = (((sint_v a * params_qinv) % pow2 16) * params_q) % pow2 16);
  lemma_mod_mul_distr_l (sint_v a * params_qinv) params_q (pow2 16);
  assert (sint_v t % pow2 16 = ((sint_v a * params_qinv) * params_q) % pow2 16);
  paren_mul_right (sint_v a) params_qinv params_q;
  lemma_mod_mul_distr_r (sint_v a) (params_qinv * params_q) (pow2 16);
  assert_norm(params_qinv * params_q % pow2 16 = 1);
  assert (sint_v t % pow2 16 = sint_v a % pow2 16);
  assert (sint_v t % params_q = 0);
  let t2:int32 = a -! t in
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
  shift_right_lemma t2 (size 16);
  assert(sint_v t3 = sint_v t2 / (pow2 16));
  euclidean_division_definition (sint_v t2) (pow2 16);
  lemma_div_le (-(pow2 16-1) * params_q) (sint_v t2) (pow2 16);
  lemma_div_le (sint_v t2) ((pow2 16) * params_q) (pow2 16);
  assert( ( - pow2 16 * params_q) / pow2 16 < sint_v t3 /\ sint_v t3 < (pow2 16 * params_q) / pow2 16);
  swap_neg_mul (pow2 16) params_q;
  cancel_mul_div params_q (pow2 16);
  cancel_mul_div (-params_q) (pow2 16);
  lemma_montgomery2 t2;
  assert ( - params_q < sint_v t3 /\ sint_v t3 < params_q);
  div_exact_r (sint_v t2) (pow2 16);
  assert ( (- pow2 31) / pow2 16 <= sint_v t3 /\ sint_v t3 < pow2 31 / pow2 16);
  pow2_minus 31 16;
  assert_norm ((-pow2 31) / pow2 16 = - pow2 15);
  assert ( - pow2 15 <= sint_v t3 /\ sint_v t3 < pow2 15);
  assert (sint_v t4 = sint_v t3);
  t4
  

(*
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
*)

#reset-options "--z3rlimit 1000 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

inline_for_extraction
val barrett_reduce_int16:
  a:int16
  -> Tot (t:int16{sint_v t % params_q = sint_v a % params_q /\ 0 <= sint_v t /\ sint_v t <= params_q})

let barrett_range_v () : Lemma (requires True) (ensures ((range ((pow2 26)/params_q+1) S16) /\ (range ((pow2 26)/params_q+1) S32))) =
  assert_norm (range ((pow2 26)/params_q + 1) S16);
  pow2_lt_compat 31 15

let barrett_range_t (a:int16) : Lemma (requires True) (ensures (range (((pow2 26)/params_q+1) * sint_v a) S32)) =
  barrett_range_v ();
  let v = i32 ((pow2 26)/params_q + 1) in
  let q = i32 params_q in
  pow2_plus 15 15;
  pow2_lt_compat 31 30;
  lemma_mult_le_left (sint_v v) (sint_v a) (pow2 15);
  lemma_mult_le_right (pow2 15) (sint_v v) (pow2 15 - 1);
  assert_norm(range (sint_v v * sint_v a) S32)

let barrett_range_t3 (a:int16) (v:int32) : Lemma (requires (sint_v v == (pow2 26)/params_q+1 )) (ensures (range (((sint_v v * sint_v a) / pow2 26) * params_q) S32)) =
  barrett_range_v ();
  let v = i32 ((pow2 26)/params_q + 1) in
  let q = i32 params_q in
  pow2_lt_compat 31 15;
  barrett_range_t a;
  let t:int32 = v *! (to_i32 a) in
  let t2 = t >>. size 26 in
  shift_right_lemma t (size 26);
  assert(sint_v t2 = sint_v t / pow2 26);
  assert(sint_v t2 = (sint_v v * sint_v a) / pow2 26);
  lemma_div_lt (sint_v v * sint_v a) 31 26;
  lemma_div_le ( - (sint_v v * sint_v a)) (pow2 31) (pow2 26);
  pow2_minus 31 16;
  assert (sint_v t >= - pow2 31);
  lemma_div_le (- pow2 31) (sint_v t) (pow2 26);
  assert_norm ( (-pow2 31) / pow2 26 = - pow2 5);
  lemma_mult_le_right params_q (sint_v t2) (pow2 5);
  euclidean_division_definition (sint_v t2) params_q;
  lemma_mult_le_right params_q (- pow2 5) (sint_v t2);
  assert_norm (pow2 5 * params_q < pow2 31);
  assert_norm (- pow2 5 * params_q > - pow2 31)

let barrett_range_t4_upperbound (a:int16) (v:int32) (t3:int32) : Lemma (requires ((sint_v v == (pow2 26)/params_q+1) /\ (sint_v t3 == ((sint_v v * sint_v a) / pow2 26) * params_q))) (ensures (sint_v a - sint_v t3 <= params_q)) =
  barrett_range_v ();
  assert_norm(range params_q S32);
  let q = i32 params_q in
  let v = i32 ((pow2 26)/params_q + 1) in
  barrett_range_t a;
  pow2_lt_compat 31 15;
  let t:int32 = v *! (to_i32 a) in
  let t2 = t >>. size 26 in
  barrett_range_t3 a v;
  division_propriety (sint_v v * sint_v a) (pow2 26);
  let t3 = t2 *! q in
  paren_mul_right (pow2 26) (sint_v t2) (params_q);
  assert(((sint_v v * sint_v a) - pow2 26) * params_q < pow2 26 * sint_v t3);
  distributivity_sub_left (sint_v v * sint_v a) (pow2 26) (params_q);
  swap_mul (sint_v v) (sint_v a);
  paren_mul_right (sint_v a) (sint_v v) params_q;
  distributivity_add_left (pow2 26 / params_q) 1 params_q;
  assert (sint_v v * params_q = pow2 26 - ((pow2 26) % params_q) + params_q);
  assert (sint_v v * params_q = pow2 26 + (params_q - ((pow2 26) % params_q)));
  distributivity_add_right (sint_v a) (pow2 26) (params_q - ((pow2 26) % params_q));
  lemma_mult_le_right (params_q - ((pow2 26) % params_q)) (- pow2 15) (sint_v a);
  assert ((sint_v a * sint_v v) * params_q >= sint_v a * pow2 26 - (pow2 15) * (params_q - ((pow2 26) % params_q)));
  distributivity_sub_left (sint_v a) params_q (pow2 26);
  assert((sint_v a - params_q) * pow2 26 - (pow2 15) * (params_q - ((pow2 26) % params_q)) <= (sint_v a * sint_v v) * params_q - pow2 26 * params_q);
  assert ((sint_v a - params_q) * pow2 26 - (pow2 15) * (params_q - ((pow2 26) % params_q)) < pow2 26 * sint_v t3);
  lemma_div_plus ( - (pow2 15) * (params_q - ((pow2 26) % params_q))) (sint_v a - params_q) (pow2 26);
  assert_norm ( ( - (pow2 15) * (params_q - ((pow2 26) % params_q))) / pow2 26 = -1);
  assert (((sint_v a - params_q) * pow2 26 - (pow2 15) * (params_q - ((pow2 26) % params_q))) / pow2 26 = (sint_v a - params_q - 1));
  lemma_div_le ((sint_v a - params_q) * pow2 26 - (pow2 15) * (params_q - ((pow2 26) % params_q))) (pow2 26 * sint_v t3) (pow2 26);
  cancel_mul_div (sint_v t3) (pow2 26);
  assert ((sint_v a - params_q - 1) <= sint_v t3);
  assert (sint_v a - params_q - 1 = sint_v t3 ==> False);
  assert (sint_v a - params_q <= sint_v t3)

let barrett_range_t4_lowerbound (a:int16) (v:int32) (t3:int32) : Lemma (requires ((sint_v v == (pow2 26)/params_q+1) /\ (sint_v t3 == ((sint_v v * sint_v a) / pow2 26) * params_q))) (ensures (sint_v a - sint_v t3 >= 0)) =
  barrett_range_v ();
  let q = i32 params_q in
  let v = i32 ((pow2 26)/params_q + 1) in
  barrett_range_t a;
  pow2_lt_compat 31 15;
  let t:int32 = v *! (to_i32 a) in
  let t2 = t >>. size 26 in
  barrett_range_t3 a v;
  division_propriety (sint_v v * sint_v a) (pow2 26);
  let t3 = t2 *! q in
  paren_mul_right (pow2 26) (sint_v t2) (params_q);
  assert(pow2 26 * sint_v t3 <= (sint_v v * sint_v a) * params_q);
  distributivity_sub_left (sint_v v * sint_v a) (pow2 26) (params_q);
  swap_mul (sint_v v) (sint_v a);
  paren_mul_right (sint_v a) (sint_v v) params_q;
  distributivity_add_left (pow2 26 / params_q) 1 params_q;
  assert (sint_v v * params_q = pow2 26 - ((pow2 26) % params_q) + params_q);
  assert (sint_v v * params_q = pow2 26 + (params_q - ((pow2 26) % params_q)));
  distributivity_add_right (sint_v a) (pow2 26) (params_q - ((pow2 26) % params_q));
  lemma_mult_le_right (params_q - ((pow2 26) % params_q)) (sint_v a) (pow2 15);
  assert ((sint_v v * sint_v a) * params_q <= sint_v a * pow2 26 + (pow2 15) * (params_q - ((pow2 26) % params_q)));
  assert (pow2 26 * sint_v t3 <= sint_v a * pow2 26 + (pow2 15) * (params_q - ((pow2 26) % params_q)));
  lemma_div_plus ((pow2 15) * (params_q - ((pow2 26) % params_q))) (sint_v a) (pow2 26);
  assert_norm (((pow2 15) * (params_q - ((pow2 26) % params_q))) / pow2 26 = 0);
  assert((sint_v a * pow2 26 + (pow2 15) * (params_q - ((pow2 26) % params_q))) / pow2 26 = sint_v a);
  lemma_div_le (pow2 26 * sint_v t3) (sint_v a * pow2 26 + (pow2 15) * (params_q - ((pow2 26) % params_q))) (pow2 26);
  swap_mul (pow2 26) (sint_v t3);
  cancel_mul_div (sint_v t3) (pow2 26);
  cancel_mul_div (sint_v a) (pow2 26)

let barrett_reduce_int16 a =
  barrett_range_v ();
  let q = i32 params_q in
  let v = i32 (normalize_term((pow2 26)/params_q + 1)) in
  assert_norm (sint_v v == ((pow2 26)/ params_q) +1);
  barrett_range_t a;
  pow2_lt_compat 31 15;
  let t:int32 = v *! (to_i32 a) in
  let t2 = t >>. size 26 in
  barrett_range_t3 a v;
  let t3 = t2 *! q in
  barrett_range_t4_lowerbound a v t3;
  barrett_range_t4_upperbound a v t3;
  assert_norm(params_q <= maxint S16 /\ 0 >= minint S16);
  let t4 = to_i16 (to_i32 a -! t3) in
  assert (0 <= sint_v t4 /\ sint_v t4 <= params_q);
  lemma_mod_plus (sint_v a) (-sint_v t2) params_q;
  t4

inline_for_extraction
val csubq_int16:
  a:int16{sint_v a - params_q >= minint S16}
  -> t:int16{if (sint_v a >= params_q) then sint_v t = sint_v a - params_q else sint_v t = sint_v a}

#reset-options "--z3rlimit 400 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let csubq_int16 a =
  assert_norm(range params_q S16);
  assert_norm(params_q >= 0);
  assert_norm(sint_v a - params_q <= sint_v a);
  assert(sint_v a <= maxint S16);
  assert(range (sint_v a - params_q) S16);
  let a2 = a -! (i16 params_q) in
  let a3 = (a2 >>. size 15) &. (i16 params_q) in
  shift_right_lemma a2 (size 15);
  assert_norm(0 / pow2 15 = 0);
  assert(sint_v a2 < pow2 15 /\ sint_v a2 >= - pow2 15);
  if (sint_v a >= params_q) then begin
    assert(sint_v a2 >= 0);
    lemma_div_lt_nat (sint_v a2) 15 15;
    lemma_div_le 0 (sint_v a2) (pow2 15);
    assert_norm(pow2 15 / pow2 15 = 1);
    assert(sint_v a2 / pow2 15 = 0);
    assert (sint_v (a2 >>. size 15) = 0)
  end
  else begin
    assert(sint_v a2 < 0);
    lemma_div_le (-pow2 15) (sint_v a2) (pow2 15);
    lemma_div_le (sint_v a2) 0 (pow2 15);
    assert_norm((-pow2 15) / pow2 15 = -1);
    assert(sint_v (a2 >>. size 15) = -1)
  end;
  logand_lemma (a2 >>. size 15) (i16 params_q);
  a2 +! a3

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

inline_for_extraction
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
  assert_norm (sint_v t / pow2 43 <= pow2 63 / pow2 43);
  assert_norm (- pow2 63 / pow2 43 <= sint_v t / pow2 43);
  pow2_lt_compat 63 43;
  pow2_lt_compat 31 20;
  assert_norm( range (sint_v t / pow2 43) S32);
  let t2:int32 = to_i32 (t >>. size 43) in
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

inline_for_extraction
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

inline_for_extraction
val division_by_q_int32:
  a:int32
  -> b:int32{sint_v b = sint_v a / params_q}

let division_by_q_int32 a =
  division_by_q_int32_cadd1_ a (division_by_q_int32_ a)

