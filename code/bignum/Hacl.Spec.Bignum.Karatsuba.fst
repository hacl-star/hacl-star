module Hacl.Spec.Bignum.Karatsuba

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Lib
open Hacl.Spec.Lib

open Hacl.Spec.Bignum.Addition
open Hacl.Spec.Bignum.Multiplication
open Hacl.Spec.Bignum.Squaring

module K = Hacl.Spec.Karatsuba.Lemmas

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let bn_mul_threshold = 32

(* this carry means nothing but the sign of the result *)
val bn_sign_abs:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> b:lbignum t aLen ->
  tuple2 (carry t) (lbignum t aLen)

let bn_sign_abs #t #aLen a b =
  let c0, t0 = bn_sub a b in
  let c1, t1 = bn_sub b a in
  let res = map2 (mask_select (uint #t 0 -. c0)) t1 t0 in
  c0, res


val bn_sign_abs_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> b:lbignum t aLen ->
  Lemma (let c, res = bn_sign_abs a b in
   bn_v res == K.abs (bn_v a) (bn_v b) /\
   v c == (if bn_v a < bn_v b then 1 else 0))

let bn_sign_abs_lemma #t #aLen a b =
  let s, r = K.sign_abs (bn_v a) (bn_v b) in

  let c0, t0 = bn_sub a b in
  bn_sub_lemma a b;
  assert (bn_v t0 - v c0 * pow2 (bits t * aLen) == bn_v a - bn_v b);

  let c1, t1 = bn_sub b a in
  bn_sub_lemma b a;
  assert (bn_v t1 - v c1 * pow2 (bits t * aLen) == bn_v b - bn_v a);

  let mask = uint #t 0 -. c0 in
  assert (v mask == (if v c0 = 0 then 0 else v (ones t SEC)));
  let res = map2 (mask_select mask) t1 t0 in
  lseq_mask_select_lemma t1 t0 mask;
  assert (bn_v res == (if v mask = 0 then bn_v t0 else bn_v t1));

  bn_eval_bound a aLen;
  bn_eval_bound b aLen;
  bn_eval_bound t0 aLen;
  bn_eval_bound t1 aLen

  // if bn_v a < bn_v b then begin
  //   assert (v mask = v (ones U64 SEC));
  //   assert (bn_v res == bn_v b - bn_v a);
  //   assert (bn_v res == r /\ v c0 = 1) end
  // else begin
  //   assert (v mask = 0);
  //   assert (bn_v res == bn_v a - bn_v b);
  //   assert (bn_v res == r /\ v c0 = 0) end;
  // assert (bn_v res == r /\ v c0 == (if bn_v a < bn_v b then 1 else 0))


val bn_middle_karatsuba:
    #t:limb_t
  -> #aLen:size_nat
  -> c0:carry t
  -> c1:carry t
  -> c2:carry t
  -> t01:lbignum t aLen
  -> t23:lbignum t aLen ->
  limb t & lbignum t aLen

let bn_middle_karatsuba #t #aLen c0 c1 c2 t01 t23 =
  let c_sign = c0 ^. c1 in
  let c3, t45 = bn_sub t01 t23 in let c3 = c2 -. c3 in
  let c4, t67 = bn_add t01 t23 in let c4 = c2 +. c4 in
  let mask = uint #t 0 -. c_sign in
  let t45 = map2 (mask_select mask) t67 t45 in
  let c5 = mask_select mask c4 c3 in
  c5, t45


val sign_lemma: #t:limb_t -> c0:carry t -> c1:carry t ->
  Lemma (v (c0 ^. c1) == (if v c0 = v c1 then 0 else 1))
let sign_lemma #t c0 c1 =
  logxor_spec c0 c1;
  match t with
  | U32 ->
    assert_norm (UInt32.logxor 0ul 0ul == 0ul);
    assert_norm (UInt32.logxor 0ul 1ul == 1ul);
    assert_norm (UInt32.logxor 1ul 0ul == 1ul);
    assert_norm (UInt32.logxor 1ul 1ul == 0ul)
  | U64 ->
    assert_norm (UInt64.logxor 0uL 0uL == 0uL);
    assert_norm (UInt64.logxor 0uL 1uL == 1uL);
    assert_norm (UInt64.logxor 1uL 0uL == 1uL);
    assert_norm (UInt64.logxor 1uL 1uL == 0uL)


val bn_middle_karatsuba_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> c0:carry t
  -> c1:carry t
  -> c2:carry t
  -> t01:lbignum t aLen
  -> t23:lbignum t aLen ->
  Lemma (let (c, res) = bn_middle_karatsuba c0 c1 c2 t01 t23 in
    let c3, t45 = bn_sub t01 t23 in let c3' = c2 -. c3 in
    let c4, t67 = bn_add t01 t23 in let c4' = c2 +. c4 in

    if v c0 = v c1 then
      v c == v c3' /\ bn_v res == bn_v t45
    else
      v c == v c4' /\ bn_v res == bn_v t67)

let bn_middle_karatsuba_lemma #t #aLen c0 c1 c2 t01 t23 =
  let lp = bn_v t01 + v c2 * pow2 (bits t * aLen) - bn_v t23 in
  let rp = bn_v t01 + v c2 * pow2 (bits t * aLen) + bn_v t23 in

  let c_sign = c0 ^. c1 in
  sign_lemma c0 c1;
  assert (v c_sign == (if v c0 = v c1 then 0 else 1));

  let c3, t45 = bn_sub t01 t23 in let c3' = c2 -. c3 in
  let c4, t67 = bn_add t01 t23 in let c4' = c2 +. c4 in

  let mask = uint #t 0 -. c_sign in
  let t45' = map2 (mask_select mask) t67 t45 in
  lseq_mask_select_lemma t67 t45 mask;
  //assert (bn_v t45' == (if v mask = 0 then bn_v t45 else bn_v t67));
  let c5 = mask_select mask c4' c3' in
  mask_select_lemma mask c4' c3'
  //assert (v c5 == (if v mask = 0 then v c3' else v c4'));


val bn_middle_karatsuba_eval_aux:
    #t:limb_t
  -> #aLen:size_nat
  -> a0:lbignum t (aLen / 2)
  -> a1:lbignum t (aLen / 2)
  -> b0:lbignum t (aLen / 2)
  -> b1:lbignum t (aLen / 2)
  -> res:lbignum t aLen
  -> c2:carry t
  -> c3:carry t -> Lemma
  (requires
    bn_v res + (v c2 - v c3) * pow2 (bits t * aLen) ==
    bn_v a0 * bn_v b1 + bn_v a1 * bn_v b0)
  (ensures  0 <= v c2 - v c3 /\ v c2 - v c3 <= 1)

let bn_middle_karatsuba_eval_aux #t #aLen a0 a1 b0 b1 res c2 c3 =
  bn_eval_bound res aLen


val bn_middle_karatsuba_eval:
    #t:limb_t
  -> #aLen:size_nat
  -> a0:lbignum t (aLen / 2)
  -> a1:lbignum t (aLen / 2)
  -> b0:lbignum t (aLen / 2)
  -> b1:lbignum t (aLen / 2)
  -> c2:carry t
  -> t01:lbignum t aLen
  -> t23:lbignum t aLen ->
  Lemma
  (requires
   (let t0 = K.abs (bn_v a0) (bn_v a1) in
    let t1 = K.abs (bn_v b0) (bn_v b1) in
    bn_v t01 + v c2 * pow2 (bits t * aLen) == bn_v a0 * bn_v b0 + bn_v a1 * bn_v b1 /\
    bn_v t23 == t0 * t1))
  (ensures
   (let c0, t0 = bn_sign_abs a0 a1 in
    let c1, t1 = bn_sign_abs b0 b1 in

    let c, res = bn_middle_karatsuba c0 c1 c2 t01 t23 in
    bn_v res + v c * pow2 (bits t * aLen) == bn_v a0 * bn_v b1 + bn_v a1 * bn_v b0))

let bn_middle_karatsuba_eval #t #aLen a0 a1 b0 b1 c2 t01 t23 =
  let pbits = bits t in
  let c0, t0 = bn_sign_abs a0 a1 in
  bn_sign_abs_lemma a0 a1;
  assert (bn_v t0 == K.abs (bn_v a0) (bn_v a1));
  assert (v c0 == (if bn_v a0 < bn_v a1 then 1 else 0));

  let c1, t1 = bn_sign_abs b0 b1 in
  bn_sign_abs_lemma b0 b1;
  assert (bn_v t1 == K.abs (bn_v b0) (bn_v b1));
  assert (v c1 == (if bn_v b0 < bn_v b1 then 1 else 0));

  let c, res = bn_middle_karatsuba c0 c1 c2 t01 t23 in
  bn_middle_karatsuba_lemma c0 c1 c2 t01 t23;

  let c3, t45 = bn_sub t01 t23 in let c3' = c2 -. c3 in
  let c4, t67 = bn_add t01 t23 in let c4' = c2 +. c4 in

  if v c0 = v c1 then begin
    assert (bn_v a0 * bn_v b0 + bn_v a1 * bn_v b1 - bn_v t0 * bn_v t1 == bn_v a0 * bn_v b1 + bn_v a1 * bn_v b0);
    assert (v c2 * pow2 (pbits * aLen) + bn_v t01 - bn_v t23 == bn_v a0 * bn_v b1 + bn_v a1 * bn_v b0);

    assert (v c == v c3' /\ bn_v res == bn_v t45);
    //assert (v c = (v c2 - v c3) % pow2 pb);
    bn_sub_lemma t01 t23;
    assert (bn_v res - v c3 * pow2 (pbits * aLen) == bn_v t01 - bn_v t23);
    Math.Lemmas.distributivity_sub_left (v c2) (v c3) (pow2 (pbits * aLen));
    assert (bn_v res + (v c2 - v c3) * pow2 (pbits * aLen) == v c2 * pow2 (pbits * aLen) + bn_v t01 - bn_v t23);
    bn_middle_karatsuba_eval_aux a0 a1 b0 b1 res c2 c3;
    Math.Lemmas.small_mod (v c2 - v c3) (pow2 pbits);
    assert (bn_v res + v c * pow2 (pbits * aLen) == v c2 * pow2 (pbits * aLen) + bn_v t01 - bn_v t23);
    () end
  else begin
    assert (bn_v a0 * bn_v b0 + bn_v a1 * bn_v b1 + bn_v t0 * bn_v t1 == bn_v a0 * bn_v b1 + bn_v a1 * bn_v b0);
    assert (v c2 * pow2 (pbits * aLen) + bn_v t01 + bn_v t23 == bn_v a0 * bn_v b1 + bn_v a1 * bn_v b0);

    assert (v c == v c4' /\ bn_v res == bn_v t67);
    //assert (v c = v c2 + v c4);
    bn_add_lemma t01 t23;
    assert (bn_v res + v c4 * pow2 (pbits * aLen) == bn_v t01 + bn_v t23);
    Math.Lemmas.distributivity_add_left (v c2) (v c4) (pow2 (pbits * aLen));
    Math.Lemmas.small_mod (v c2 + v c4) (pow2 pbits);
    assert (bn_v res + v c * pow2 (pbits * aLen) == v c2 * pow2 (pbits * aLen) + bn_v t01 + bn_v t23);
    () end


val bn_lshift_add:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> b1:limb t
  -> i:nat{i + 1 <= aLen} ->
  tuple2 (carry t) (lbignum t aLen)

let bn_lshift_add #t #aLen a b1 i =
  let r = sub a i (aLen - i) in
  let c, r' = bn_add1 r b1 in
  let a' = update_sub a i (aLen - i) r' in
  c, a'


val bn_lshift_add_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> b1:limb t
  -> i:nat{i + 1 <= aLen} ->
  Lemma (let c, res = bn_lshift_add a b1 i in
    bn_v res + v c * pow2 (bits t * aLen) == bn_v a + v b1 * pow2 (bits t * i))

let bn_lshift_add_lemma #t #aLen a b1 i =
  let pbits = bits t in
  let r = sub a i (aLen - i) in
  let c, r' = bn_add1 r b1 in
  let a' = update_sub a i (aLen - i) r' in
  let p = pow2 (pbits * aLen) in

  calc (==) {
    bn_v a' + v c * p;
    == { bn_update_sub_eval a r' i }
    bn_v a - bn_v r * pow2 (pbits * i) + bn_v r' * pow2 (pbits * i) + v c * p;
    == { bn_add1_lemma r b1 }
    bn_v a - bn_v r * pow2 (pbits * i) + (bn_v r + v b1 - v c * pow2 (pbits * (aLen - i))) * pow2 (pbits * i) + v c * p;
    == { Math.Lemmas.distributivity_add_left (bn_v r) (v b1 - v c * pow2 (pbits * (aLen - i))) (pow2 (pbits * i)) }
    bn_v a + (v b1 - v c * pow2 (pbits * (aLen - i))) * pow2 (pbits * i) + v c * p;
    == { Math.Lemmas.distributivity_sub_left (v b1) (v c * pow2 (pbits * (aLen - i))) (pow2 (pbits * i)) }
    bn_v a + v b1 * pow2 (pbits * i) - (v c * pow2 (pbits * (aLen - i))) * pow2 (pbits * i) + v c * p;
    == { Math.Lemmas.paren_mul_right (v c) (pow2 (pbits * (aLen - i))) (pow2 (pbits * i));
           Math.Lemmas.pow2_plus (pbits * (aLen - i)) (pbits * i) }
    bn_v a + v b1 * pow2 (pbits * i);
    }


val bn_lshift_add_early_stop:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat
  -> a:lbignum t aLen
  -> b:lbignum t bLen
  -> i:nat{i + bLen <= aLen} ->
  tuple2 (carry t) (lbignum t aLen)

let bn_lshift_add_early_stop #t #aLen #bLen a b i =
  let r = sub a i bLen in
  let c, r' = bn_add r b in
  let a' = update_sub a i bLen r' in
  c, a'


val bn_lshift_add_early_stop_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat
  -> a:lbignum t aLen
  -> b:lbignum t bLen
  -> i:nat{i + bLen <= aLen} ->
  Lemma (let c, res = bn_lshift_add_early_stop a b i in
    bn_v res + v c * pow2 (bits t * (i + bLen)) == bn_v a + bn_v b * pow2 (bits t * i))

let bn_lshift_add_early_stop_lemma #t #aLen #bLen a b i =
  let pbits = bits t in
  let r = sub a i bLen in
  let c, r' = bn_add r b in
  let a' = update_sub a i bLen r' in
  let p = pow2 (pbits * (i + bLen)) in

  calc (==) {
    bn_v a' + v c * p;
    == { bn_update_sub_eval a r' i }
    bn_v a - bn_v r * pow2 (pbits * i) + bn_v r' * pow2 (pbits * i) + v c * p;
    == { bn_add_lemma r b }
    bn_v a - bn_v r * pow2 (pbits * i) + (bn_v r + bn_v b - v c * pow2 (pbits * bLen)) * pow2 (pbits * i) + v c * p;
    == { Math.Lemmas.distributivity_add_left (bn_v r) (bn_v b - v c * pow2 (pbits * bLen)) (pow2 (pbits * i)) }
    bn_v a + (bn_v b - v c * pow2 (pbits * bLen)) * pow2 (pbits * i) + v c * p;
    == { Math.Lemmas.distributivity_sub_left  (bn_v b) (v c * pow2 (pbits * bLen)) (pow2 (pbits * i)) }
    bn_v a + bn_v b * pow2 (pbits * i) - (v c * pow2 (pbits * bLen)) * pow2 (pbits * i) + v c * p;
    == { Math.Lemmas.paren_mul_right (v c) (pow2 (pbits * bLen)) (pow2 (pbits * i));
           Math.Lemmas.pow2_plus (pbits * bLen) (pbits * i) }
    bn_v a + bn_v b * pow2 (pbits * i);
    }


val bn_karatsuba_res:
    #t:limb_t
  -> #aLen:size_pos{2 * aLen <= max_size_t}
  -> r01:lbignum t aLen
  -> r23:lbignum t aLen
  -> c5:limb t
  -> t45:lbignum t aLen ->
  tuple2 (carry t) (lbignum t (aLen + aLen))

let bn_karatsuba_res #t #aLen r01 r23 c5 t45 =
  let aLen2 = aLen / 2 in
  let res = concat r01 r23 in

  let c6, res = bn_lshift_add_early_stop res t45 aLen2 in
  // let r12 = sub res aLen2 aLen in
  // let c6, r12 = bn_add r12 t45 in
  // let res = update_sub res aLen2 aLen r12 in

  let c7 = c5 +. c6 in
  let c8, res = bn_lshift_add res c7 (aLen + aLen2) in
  // let r3 = sub res (aLen + aLen2) aLen2 in
  // let _, r3 = bn_add r3 (create 1 c7) in
  // let res = update_sub res (aLen + aLen2) aLen2 r3 in
  c8, res


val bn_karatsuba_res_lemma:
    #t:limb_t
  -> #aLen:size_pos{2 * aLen <= max_size_t}
  -> r01:lbignum t aLen
  -> r23:lbignum t aLen
  -> c5:limb t{v c5 <= 1}
  -> t45:lbignum t aLen ->
  Lemma
   (let c, res = bn_karatsuba_res r01 r23 c5 t45 in
    bn_v res + v c * pow2 (bits t * (aLen + aLen)) ==
    bn_v r23 * pow2 (bits t * aLen) + (v c5 * pow2 (bits t * aLen) + bn_v t45) * pow2 (aLen / 2 * bits t) + bn_v r01)

let bn_karatsuba_res_lemma #t #aLen r01 r23 c5 t45 =
  let pbits = bits t in
  let aLen2 = aLen / 2 in
  let aLen3 = aLen + aLen2 in
  let aLen4 = aLen + aLen in

  let res0 = concat r01 r23 in
  let c6, res1 = bn_lshift_add_early_stop res0 t45 aLen2 in

  let c7 = c5 +. c6 in
  let c8, res2 = bn_lshift_add res1 c7 aLen3 in

  calc (==) {
    bn_v res2 + v c8 * pow2 (pbits * aLen4);
    == { bn_lshift_add_lemma res1 c7 aLen3 }
    bn_v res1 + v c7 * pow2 (pbits * aLen3);
    == { Math.Lemmas.small_mod (v c5 + v c6) (pow2 pbits) }
    bn_v res1 + (v c5 + v c6) * pow2 (pbits * aLen3);
    == { bn_lshift_add_early_stop_lemma res0 t45 aLen2 }
    bn_v res0 + bn_v t45 * pow2 (pbits * aLen2) - v c6 * pow2 (pbits * aLen3) + (v c5 + v c6) * pow2 (pbits * aLen3);
    == { Math.Lemmas.distributivity_add_left (v c5) (v c6) (pow2 (pbits * aLen3)) }
    bn_v res0 + bn_v t45 * pow2 (pbits * aLen2) + v c5 * pow2 (pbits * aLen3);
    == { Math.Lemmas.pow2_plus (pbits * aLen) (pbits * aLen2) }
    bn_v res0 + bn_v t45 * pow2 (pbits * aLen2) + v c5 * (pow2 (pbits * aLen) * pow2 (pbits * aLen2));
    == { Math.Lemmas.paren_mul_right (v c5) (pow2 (pbits * aLen)) (pow2 (pbits * aLen2));
      Math.Lemmas.distributivity_add_left (bn_v t45) (v c5 * pow2 (pbits * aLen)) (pow2 (pbits * aLen2)) }
    bn_v res0 + (bn_v t45 + v c5 * pow2 (pbits * aLen)) * pow2 (pbits * aLen2);
    == { bn_concat_lemma r01 r23 }
    bn_v r23 * pow2 (pbits * aLen) + (v c5 * pow2 (pbits * aLen) + bn_v t45) * pow2 (pbits * aLen2) + bn_v r01;
    }


val bn_middle_karatsuba_carry_bound:
    #t:limb_t
  -> aLen:size_nat{aLen % 2 = 0}
  -> a0:lbignum t (aLen / 2)
  -> a1:lbignum t (aLen / 2)
  -> b0:lbignum t (aLen / 2)
  -> b1:lbignum t (aLen / 2)
  -> res:lbignum t aLen
  -> c:limb t -> Lemma
  (requires bn_v res + v c * pow2 (bits t * aLen) == bn_v a0 * bn_v b1 + bn_v a1 * bn_v b0)
  (ensures  v c <= 1)

let bn_middle_karatsuba_carry_bound #t aLen a0 a1 b0 b1 res c =
  let pbits = bits t in
  let aLen2 = aLen / 2 in
  let p = pow2 (pbits * aLen2) in
  bn_eval_bound a0 aLen2;
  bn_eval_bound a1 aLen2;
  bn_eval_bound b0 aLen2;
  bn_eval_bound b1 aLen2;

  calc (<) {
    bn_v a0 * bn_v b1 + bn_v a1 * bn_v b0;
    < { Math.Lemmas.lemma_mult_lt_sqr (bn_v a0) (bn_v b1) p }
    p * p + bn_v a1 * bn_v b0;
    < { Math.Lemmas.lemma_mult_lt_sqr (bn_v a1) (bn_v b0) p }
    p * p + p * p;
    == { K.lemma_double_p (bits t) aLen }
    pow2 (pbits * aLen) + pow2 (pbits * aLen);
    };

  bn_eval_bound res aLen;
  assert (bn_v res + v c * pow2 (pbits * aLen) < pow2 (pbits * aLen) + pow2 (pbits * aLen));
  assert (v c <= 1)


val bn_karatsuba_no_last_carry:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t aLen
  -> c:carry t
  -> res:lbignum t (aLen + aLen) -> Lemma
  (requires bn_v res + v c * pow2 (bits t * (aLen + aLen)) == bn_v a * bn_v b)
  (ensures  v c == 0)

let bn_karatsuba_no_last_carry #t #aLen a b c res =
  bn_eval_bound a aLen;
  bn_eval_bound b aLen;
  Math.Lemmas.lemma_mult_lt_sqr (bn_v a) (bn_v b) (pow2 (bits t * aLen));
  Math.Lemmas.pow2_plus (bits t * aLen) (bits t * aLen);
  bn_eval_bound res (aLen + aLen)


val bn_karatsuba_mul_:
    #t:limb_t
  -> aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t aLen ->
  Tot (res:lbignum t (aLen + aLen){bn_v res == bn_v a * bn_v b}) (decreases aLen)

let rec bn_karatsuba_mul_ #t aLen a b =
  if aLen < bn_mul_threshold || aLen % 2 = 1 then begin
    bn_mul_lemma a b;
    bn_mul a b end
  else begin
    let aLen2 = aLen / 2 in
    let a0 = bn_mod_pow2 a aLen2 in
    (**) bn_mod_pow2_lemma a aLen2;
    let a1 = bn_div_pow2 a aLen2 in
    (**) bn_div_pow2_lemma a aLen2;

    let b0 = bn_mod_pow2 b aLen2 in
    (**) bn_mod_pow2_lemma b aLen2;
    let b1 = bn_div_pow2 b aLen2 in
    (**) bn_div_pow2_lemma b aLen2;
    (**) bn_eval_bound a aLen;
    (**) bn_eval_bound b aLen;
    (**) K.lemma_bn_halves (bits t) aLen (bn_v a);
    (**) K.lemma_bn_halves (bits t) aLen (bn_v b);

    let c0, t0 = bn_sign_abs a0 a1 in
    (**) bn_sign_abs_lemma a0 a1;
    let c1, t1 = bn_sign_abs b0 b1 in
    (**) bn_sign_abs_lemma b0 b1;

    let t23 = bn_karatsuba_mul_ aLen2 t0 t1 in
    let r01 = bn_karatsuba_mul_ aLen2 a0 b0 in
    let r23 = bn_karatsuba_mul_ aLen2 a1 b1 in

    let c2, t01 = bn_add r01 r23 in
    (**) bn_add_lemma r01 r23;
    let c5, t45 = bn_middle_karatsuba c0 c1 c2 t01 t23 in
    (**) bn_middle_karatsuba_eval a0 a1 b0 b1 c2 t01 t23;
    (**) bn_middle_karatsuba_carry_bound aLen a0 a1 b0 b1 t45 c5;

    let c, res = bn_karatsuba_res r01 r23 c5 t45 in
    (**) bn_karatsuba_res_lemma r01 r23 c5 t45;
    (**) K.lemma_karatsuba (bits t) aLen (bn_v a0) (bn_v a1) (bn_v b0) (bn_v b1);
    (**) bn_karatsuba_no_last_carry a b c res;
    assert (v c = 0);
    res end


val bn_karatsuba_mul:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t aLen ->
  lbignum t (aLen + aLen)

let bn_karatsuba_mul #t #aLen a b =
  bn_karatsuba_mul_ aLen a b


val bn_karatsuba_mul_lemma:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t aLen ->
  Lemma (bn_karatsuba_mul a b == bn_mul a b /\
    bn_v (bn_karatsuba_mul a b) == bn_v a * bn_v b)

let bn_karatsuba_mul_lemma #t #aLen a b =
  let res = bn_karatsuba_mul_ aLen a b in
  assert (bn_v res == bn_v a * bn_v b);
  let res' = bn_mul a b in
  bn_mul_lemma a b;
  assert (bn_v res' == bn_v a * bn_v b);
  bn_eval_inj (aLen + aLen) res res';
  assert (bn_karatsuba_mul_ aLen a b == bn_mul a b)


val bn_middle_karatsuba_sqr:
    #t:limb_t
  -> #aLen:size_nat
  -> c2:carry t
  -> t01:lbignum t aLen
  -> t23:lbignum t aLen ->
  limb t & lbignum t aLen

let bn_middle_karatsuba_sqr #t #aLen c2 t01 t23 =
  let c3, t45 = bn_sub t01 t23 in let c3 = c2 -. c3 in
  c3, t45


val bn_middle_karatsuba_sqr_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> c0:carry t
  -> c2:carry t
  -> t01:lbignum t aLen
  -> t23:lbignum t aLen ->
  Lemma (bn_middle_karatsuba_sqr c2 t01 t23 == bn_middle_karatsuba c0 c0 c2 t01 t23)

let bn_middle_karatsuba_sqr_lemma #t #aLen c0 c2 t01 t23 =
  let (c, res) = bn_middle_karatsuba c0 c0 c2 t01 t23 in
  let c3, t45 = bn_sub t01 t23 in let c3' = c2 -. c3 in
  bn_middle_karatsuba_lemma c0 c0 c2 t01 t23;
  assert (v c == v c3' /\ bn_v res == bn_v t45);
  bn_eval_inj aLen t45 res


val bn_karatsuba_sqr_: #t:limb_t -> aLen:size_nat{aLen + aLen <= max_size_t} -> a:lbignum t aLen ->
  Tot (res:lbignum t (aLen + aLen){bn_v res == bn_v a * bn_v a}) (decreases aLen)

let rec bn_karatsuba_sqr_ #t aLen a =
  if aLen < bn_mul_threshold || aLen % 2 = 1 then begin
    bn_sqr_lemma a;
    bn_sqr a end
  else begin
    let aLen2 = aLen / 2 in
    let a0 = bn_mod_pow2 a aLen2 in
    (**) bn_mod_pow2_lemma a aLen2;
    let a1 = bn_div_pow2 a aLen2 in
    (**) bn_div_pow2_lemma a aLen2;
    (**) bn_eval_bound a aLen;
    (**) K.lemma_bn_halves (bits t) aLen (bn_v a);

    let c0, t0 = bn_sign_abs a0 a1 in
    (**) bn_sign_abs_lemma a0 a1;

    let t23 = bn_karatsuba_sqr_ aLen2 t0 in
    let r01 = bn_karatsuba_sqr_ aLen2 a0 in
    let r23 = bn_karatsuba_sqr_ aLen2 a1 in

    let c2, t01 = bn_add r01 r23 in
    (**) bn_add_lemma r01 r23;
    let c5, t45 = bn_middle_karatsuba_sqr c2 t01 t23 in
    (**) bn_middle_karatsuba_sqr_lemma c0 c2 t01 t23;
    (**) bn_middle_karatsuba_eval a0 a1 a0 a1 c2 t01 t23;
    (**) bn_middle_karatsuba_carry_bound aLen a0 a1 a0 a1 t45 c5;

    let c, res = bn_karatsuba_res r01 r23 c5 t45 in
    (**) bn_karatsuba_res_lemma r01 r23 c5 t45;
    (**) K.lemma_karatsuba (bits t) aLen (bn_v a0) (bn_v a1) (bn_v a0) (bn_v a1);
    (**) bn_karatsuba_no_last_carry a a c res;
    assert (v c = 0);
    res end


val bn_karatsuba_sqr:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen ->
  lbignum t (aLen + aLen)

let bn_karatsuba_sqr #t #aLen a =
  bn_karatsuba_sqr_ aLen a


val bn_karatsuba_sqr_lemma:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen ->
  Lemma (bn_karatsuba_sqr a == bn_mul a a /\
    bn_v (bn_karatsuba_sqr a) == bn_v a * bn_v a)

let bn_karatsuba_sqr_lemma #t #aLen a =
  let res = bn_karatsuba_sqr_ aLen a in
  assert (bn_v res == bn_v a * bn_v a);
  let res' = bn_mul a a in
  bn_mul_lemma a a;
  assert (bn_v res' == bn_v a * bn_v a);
  bn_eval_inj (aLen + aLen) res res';
  assert (bn_karatsuba_sqr_ aLen a == bn_mul a a)
