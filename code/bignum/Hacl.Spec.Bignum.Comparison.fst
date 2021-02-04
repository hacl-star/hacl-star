module Hacl.Spec.Bignum.Comparison

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum.Lib

module BSeq = Lib.ByteSequence
module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  Bignum comparison and test functions
///

val bn_is_odd: #t:limb_t -> #len:size_pos -> a:lbignum t len -> limb t
let bn_is_odd #t #len b = b.[0] &. uint #t 1

val bn_is_odd_lemma: #t:limb_t -> #len:size_pos -> a:lbignum t len ->
  Lemma (v (bn_is_odd a) == (bn_v a % 2))
let bn_is_odd_lemma #t #len b =
  let pbits = bits t in
  bn_eval_split_i b 1;
  bn_eval1 (slice b 0 1);
  assert (bn_v b % 2 == (v b.[0] + pow2 pbits * bn_v (slice b 1 len)) % 2);
  Math.Lemmas.pow2_plus 1 (pbits - 1);
  Math.Lemmas.modulo_addition_lemma (v b.[0]) 2 (pow2 (pbits - 1) * bn_v (slice b 1 len));
  assert (bn_v b % 2 == v b.[0] % 2);
  mod_mask_lemma b.[0] 1ul;
  assert (v (mod_mask #t #SEC 1ul) == v (uint #t #SEC 1))


val bn_eq_mask: #t:limb_t -> #len:size_nat -> a:lbignum t len -> b:lbignum t len -> limb t
let bn_eq_mask #t #len a b =
  BSeq.seq_eq_mask a b len

val bn_eq_mask_lemma: #t:limb_t -> #len:size_nat -> a:lbignum t len -> b:lbignum t len ->
  Lemma (mask_values (bn_eq_mask a b) /\
    (if v (bn_eq_mask a b) = 0 then bn_v a <> bn_v b else bn_v a = bn_v b))
let bn_eq_mask_lemma #t #len a b =
  let mask = BSeq.seq_eq_mask a b len in
  assert (a == b ==> v mask == v (ones t SEC));
  assert (a =!= b ==> v mask == v (zeros t SEC));
  Classical.move_requires_2 (bn_eval_inj len) a b


val bn_is_zero_mask: #t:limb_t -> #len:size_nat -> a:lbignum t len -> limb t
let bn_is_zero_mask #t #len b =
  let bn_zero = create len (uint #t 0) in
  bn_eq_mask b bn_zero

val bn_is_zero_mask_lemma: #t:limb_t -> #len:size_nat -> a:lbignum t len ->
  Lemma (mask_values (bn_is_zero_mask a) /\
    (if v (bn_is_zero_mask a) = 0 then bn_v a <> 0 else bn_v a = 0))
let bn_is_zero_mask_lemma #t #len b =
  let bn_zero = create len (uint #t 0) in
  bn_eval_zeroes #t len len;
  bn_eq_mask_lemma b bn_zero


val bn_lt_mask_f: #t:limb_t -> #len:size_nat -> a:lbignum t len -> b:lbignum t len -> i:nat{i < len} -> acc:limb t -> limb t
let bn_lt_mask_f #t #len a b i acc =
  let beq = eq_mask a.[i] b.[i] in
  let blt = lt_mask a.[i] b.[i] in
  mask_select beq acc (mask_select blt (ones t SEC) (zeros t SEC))

let bn_lt_mask_t (t:limb_t) (len:size_nat) (i:nat{i <= len}) = limb t

val bn_lt_mask: #t:limb_t -> #len:size_nat -> a:lbignum t len -> b:lbignum t len -> limb t
let bn_lt_mask #t #len a b =
  Loops.repeat_gen len (bn_lt_mask_t t len) (bn_lt_mask_f a b) (uint #t 0)


val bn_lt_mask_lemma_step:
    #t:limb_t
  -> #len:size_nat
  -> a:lbignum t len
  -> b:lbignum t len
  -> k:pos{k <= len}
  -> mask0:limb t -> Lemma
  (requires
    (if v mask0 = 0 then eval_ len a (k - 1) >= eval_ len b (k - 1) else eval_ len a (k - 1) < eval_ len b (k - 1)) /\
    mask_values mask0)
  (ensures (let mask = bn_lt_mask_f a b (k - 1) mask0 in
    (if v mask = 0 then eval_ len a k >= eval_ len b k else eval_ len a k < eval_ len b k) /\
    mask_values mask))

let bn_lt_mask_lemma_step #t #len a b k mask0 =
  let mask = bn_lt_mask_f a b (k - 1) mask0 in
  let ai = a.[k - 1] in
  let bi = b.[k - 1] in
  let beq = eq_mask ai bi in
  assert (if v ai = v bi then v beq == v (ones t SEC) else v beq == 0);
  let blt = lt_mask ai bi in
  assert (if v ai < v bi then v blt == v (ones t SEC) else v blt == 0);

  let res0 = mask_select blt (ones t SEC) (zeros t SEC) in
  let mask = mask_select beq mask0 res0 in
  //assert (mask == bn_lt_mask_f #len a b (k - 1) mask0);

  mask_select_lemma blt (ones t SEC) (zeros t SEC);
  mask_select_lemma beq mask0 res0;

  if v beq = 0 then begin
    assert (v mask = v res0);
    mask_select_lemma blt (ones t SEC) (zeros t SEC);
    //assert (v res0 == (if v blt = 0 then 0 else v (ones t SEC)));
    assert (if v mask = 0 then v ai > v bi else v ai < v bi);
    if v a.[k - 1] < v b.[k - 1] then bn_eval_lt len a b k else bn_eval_lt len b a k;
    () end
  else begin
    assert (v mask = v mask0);
    //assert (v beq == v (ones t SEC));
    //assert (if v mask = v mask0 then v ai = v bi else v ai <> v bi);
    assert (v ai == v bi);
    bn_eval_unfold_i a k;
    bn_eval_unfold_i b k;
    () end


val bn_lt_mask_lemma_loop:
    #t:limb_t
  -> #len:size_nat
  -> a:lbignum t len
  -> b:lbignum t len
  -> k:nat{k <= len} ->
  Lemma (let mask = Loops.repeat_gen k (bn_lt_mask_t t len) (bn_lt_mask_f a b) (uint #t 0) in
   mask_values mask /\ (if v mask = 0 then eval_ len a k >= eval_ len b k else eval_ len a k < eval_ len b k))

let rec bn_lt_mask_lemma_loop #t #len a b k =
  let mask = Loops.repeat_gen k (bn_lt_mask_t t len) (bn_lt_mask_f a b) (uint #t 0) in
  if k = 0 then begin
    Loops.eq_repeat_gen0 k (bn_lt_mask_t t len) (bn_lt_mask_f a b) (uint #t 0);
    assert (v mask = 0);
    bn_eval0 a;
    bn_eval0 b end
  else begin
    let mask0 = Loops.repeat_gen (k - 1) (bn_lt_mask_t t len) (bn_lt_mask_f a b) (uint #t 0) in
    Loops.unfold_repeat_gen k (bn_lt_mask_t t len) (bn_lt_mask_f a b) (uint #t 0) (k - 1);
    bn_lt_mask_lemma_loop a b (k - 1);
    bn_lt_mask_lemma_step a b k mask0 end


val bn_lt_mask_lemma: #t:limb_t -> #len:size_nat -> a:lbignum t len -> b:lbignum t len ->
  Lemma (mask_values (bn_lt_mask a b) /\
    (if v (bn_lt_mask a b) = 0 then bn_v a >= bn_v b else bn_v a < bn_v b))
let bn_lt_mask_lemma #t #len a b =
  bn_lt_mask_lemma_loop a b len


val bn_lt_pow2_mask: #t:limb_t -> #len:size_nat -> b:lbignum t len -> x:size_nat{x < bits t * len} -> limb t
let bn_lt_pow2_mask #t #len b x =
  let b2 = create len (uint #t 0) in
  let b2 = bn_set_ith_bit b2 x in
  bn_lt_mask b b2

val bn_lt_pow2_mask_lemma: #t:limb_t -> #len:size_nat -> b:lbignum t len -> x:size_nat{x < bits t * len} ->
  Lemma (mask_values (bn_lt_pow2_mask b x) /\
    (if v (bn_lt_pow2_mask b x) = 0 then bn_v b >= pow2 x else bn_v b < pow2 x))
let bn_lt_pow2_mask_lemma #t #len b x =
  bn_eval_bound b len;
  assert (bn_v b < pow2 (bits t * len));
  let b2 = create len (uint #t 0) in
  bn_eval_zeroes #t len len;
  assert (bn_v b2 = 0);
  //assert (bn_v b2 < pow2 x);
  let b2' = bn_set_ith_bit b2 x in
  bn_set_ith_bit_lemma b2 x;
  assert (bn_v b2' == pow2 x);
  bn_lt_mask_lemma b b2'


val bn_gt_pow2_mask: #t:limb_t -> #len:size_nat -> b:lbignum t len -> x:size_nat{x < bits t * len} -> limb t
let bn_gt_pow2_mask #t #len b x =
  let b2 = create len (uint #t 0) in
  let b2 = bn_set_ith_bit b2 x in
  bn_lt_mask b2 b

val bn_gt_pow2_mask_lemma: #t:limb_t -> #len:size_nat -> b:lbignum t len -> x:size_nat{x < bits t * len} ->
  Lemma (mask_values (bn_gt_pow2_mask b x) /\
    (if v (bn_gt_pow2_mask b x) = 0 then pow2 x >= bn_v b else pow2 x < bn_v b))
let bn_gt_pow2_mask_lemma #t #len b x =
  bn_eval_bound b len;
  assert (bn_v b < pow2 (bits t * len));
  let b2 = create len (uint #t 0) in
  bn_eval_zeroes #t len len;
  assert (bn_v b2 = 0);
  //assert (bn_v b2 < pow2 x);
  let b2' = bn_set_ith_bit b2 x in
  bn_set_ith_bit_lemma b2 x;
  assert (bn_v b2' == pow2 x);
  bn_lt_mask_lemma b2' b
