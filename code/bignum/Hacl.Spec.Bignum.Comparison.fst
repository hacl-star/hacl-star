module Hacl.Spec.Bignum.Comparison

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum.Lib

module BSeq = Lib.ByteSequence
module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  Bignum comparison and test functions
///

val bn_is_zero: #len:size_nat -> a:lbignum len -> bool
let bn_is_zero #len b =
  let bn_zero = create len (u64 0) in
  let mask = BSeq.seq_eq_mask b bn_zero len in
  FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 mask =^ ones U64 PUB)

val bn_is_zero_lemma: #len:size_nat -> a:lbignum len -> Lemma
  (bn_is_zero #len a == (bn_v a = 0))
let bn_is_zero_lemma #len b =
  let bn_zero = create len (u64 0) in
  bn_eval_zeroes len len;
  let mask = BSeq.seq_eq_mask b bn_zero len in
  assert (b == bn_zero ==> v mask == v (ones U64 SEC));
  assert (b =!= bn_zero ==> v mask == v (zeros U64 SEC));
  Classical.move_requires_2 (bn_eval_inj len) b bn_zero;
  assert (bn_is_zero #len b == (if bn_v b = bn_v bn_zero then true else false))


val bn_is_odd: #len:size_nat -> a:lbignum len -> bool
let bn_is_odd #len b =
  if len > 0 then
    FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 (b.[0] &. u64 1) =^ 1uL)
  else false

val bn_is_odd_lemma: #len:size_nat -> a:lbignum len -> Lemma
  (bn_is_odd #len a == (bn_v a % 2 = 1))
let bn_is_odd_lemma #len b =
  if len > 0 then begin
    bn_eval_split_i #len b 1;
    bn_eval1 (slice b 0 1);
    assert (bn_v b % 2 == (v b.[0] + pow2 64 * bn_v (slice b 1 len)) % 2);
    Math.Lemmas.pow2_plus 1 63;
    Math.Lemmas.modulo_addition_lemma (v b.[0]) 2 (pow2 63 * bn_v (slice b 1 len));
    assert (bn_v b % 2 == v b.[0] % 2);
    mod_mask_lemma b.[0] 1ul;
    assert (v (mod_mask #U64 #SEC 1ul) == v (u64 1)) end
  else bn_eval0 #len b


val bn_mask_lt_f: #len:size_nat -> a:lbignum len -> b:lbignum len -> i:nat{i < len} -> acc:uint64 -> uint64
let bn_mask_lt_f #len a b i acc =
  let beq = eq_mask a.[i] b.[i] in
  let blt = lt_mask a.[i] b.[i] in
  mask_select beq acc (mask_select blt (ones U64 SEC) (zeros U64 SEC))

let bn_mask_lt_t (len:size_nat) (i:nat{i <= len}) = uint64

val bn_mask_lt: #len:size_nat -> a:lbignum len -> b:lbignum len -> uint64
let bn_mask_lt #len a b =
  Loops.repeat_gen len (bn_mask_lt_t len) (bn_mask_lt_f #len a b) (u64 0)

val bn_mask_lt_lemma_step:
  #len:size_nat -> a:lbignum len -> b:lbignum len -> k:pos{k <= len} -> mask0:uint64 -> Lemma
  (requires
    (if v mask0 = 0 then eval_ len a (k - 1) >= eval_ len b (k - 1) else eval_ len a (k - 1) < eval_ len b (k - 1)) /\
    (v mask0 == 0 \/ v mask0 == v (ones U64 SEC)))
  (ensures (let mask = bn_mask_lt_f #len a b (k - 1) mask0 in
    (if v mask = 0 then eval_ len a k >= eval_ len b k else eval_ len a k < eval_ len b k) /\
    (v mask == 0 \/ v mask == v (ones U64 SEC))))

let bn_mask_lt_lemma_step #len a b k mask0 =
  let mask = bn_mask_lt_f #len a b (k - 1) mask0 in
  let ai = a.[k - 1] in
  let bi = b.[k - 1] in
  let beq = eq_mask ai bi in
  assert (if v ai = v bi then v beq == v (ones U64 SEC) else v beq == 0);
  let blt = lt_mask ai bi in
  assert (if v ai < v bi then v blt == v (ones U64 SEC) else v blt == 0);

  let res0 = mask_select blt (ones U64 SEC) (zeros U64 SEC) in
  let mask = mask_select beq mask0 res0 in
  //assert (mask == bn_mask_lt_f #len a b (k - 1) mask0);

  mask_select_lemma blt (ones U64 SEC) (zeros U64 SEC);
  mask_select_lemma beq mask0 res0;

  if v beq = 0 then begin
    assert (v mask = v res0);
    mask_select_lemma blt (ones U64 SEC) (zeros U64 SEC);
    //assert (v res0 == (if v blt = 0 then 0 else v (ones U64 SEC)));
    assert (if v mask = 0 then v ai > v bi else v ai < v bi);
    if v a.[k - 1] < v b.[k - 1] then bn_eval_lt len a b k else bn_eval_lt len b a k;
    () end
  else begin
    assert (v mask = v mask0);
    //assert (v beq == v (ones U64 SEC));
    //assert (if v mask = v mask0 then v ai = v bi else v ai <> v bi);
    assert (v ai == v bi);
    bn_eval_unfold_i a k;
    bn_eval_unfold_i b k;
    () end


val bn_mask_lt_lemma_loop:
  #len:size_nat -> a:lbignum len -> b:lbignum len -> k:nat{k <= len} -> Lemma
  (let mask = Loops.repeat_gen k (bn_mask_lt_t len) (bn_mask_lt_f #len a b) (u64 0) in
   (v mask == 0 \/ v mask == v (ones U64 SEC)) /\
   (if v mask = 0 then eval_ len a k >= eval_ len b k else eval_ len a k < eval_ len b k))

let rec bn_mask_lt_lemma_loop #len a b k =
  let mask = Loops.repeat_gen k (bn_mask_lt_t len) (bn_mask_lt_f #len a b) (u64 0) in
  if k = 0 then begin
    Loops.eq_repeat_gen0 k (bn_mask_lt_t len) (bn_mask_lt_f #len a b) (u64 0);
    assert (v mask = 0);
    bn_eval0 a;
    bn_eval0 b end
  else begin
    let mask0 = Loops.repeat_gen (k - 1) (bn_mask_lt_t len) (bn_mask_lt_f #len a b) (u64 0) in
    Loops.unfold_repeat_gen k (bn_mask_lt_t len) (bn_mask_lt_f #len a b) (u64 0) (k - 1);
    bn_mask_lt_lemma_loop #len a b (k - 1);
    bn_mask_lt_lemma_step #len a b k mask0 end

val bn_mask_lt_lemma: #len:size_nat -> a:lbignum len -> b:lbignum len -> Lemma
  (let mask = bn_mask_lt a b in
   (v mask = 0 \/ v mask = v (ones U64 SEC)) /\
   (if v mask = 0 then bn_v a >= bn_v b else bn_v a < bn_v b))

let bn_mask_lt_lemma #len a b =
  bn_mask_lt_lemma_loop #len a b len


val bn_is_less: #len:size_nat -> a:lbignum len -> b:lbignum len -> bool
let bn_is_less #len a b =
  let mask = bn_mask_lt a b in
  FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 mask =^ ones U64 PUB)

val bn_is_less_lemma: #len:size_nat -> a:lbignum len -> b:lbignum len -> Lemma
  (bn_is_less a b == (bn_v a < bn_v b))
let bn_is_less_lemma #len a b =
  bn_mask_lt_lemma #len a b


// we could compare bBits with x, but we don't have the bn_num_bits function
// bn_v b < pow2 x
val bn_lt_pow2: #len:size_nat -> b:lbignum len -> x:size_nat -> bool
let bn_lt_pow2 #len b x =
  if x >= 64 * len then true
  else begin
    let b2 = create len (u64 0) in
    let b2 = bn_bit_set b2 x in
    bn_is_less b b2 end

val bn_lt_pow2_lemma: #len:size_nat -> b:lbignum len -> x:size_nat -> Lemma
  (bn_lt_pow2 #len b x == (bn_v b < pow2 x))
let bn_lt_pow2_lemma #len b x =
  bn_eval_bound #len b len;
  assert (bn_v b < pow2 (64 * len));
  if x >= 64 * len then
    Math.Lemmas.pow2_le_compat x (64 * len)
  else begin
    let b2 = create len (u64 0) in
    bn_eval_zeroes len len;
    assert (bn_v b2 = 0);
    //assert (bn_v b2 < pow2 x);
    let b2' = bn_bit_set b2 x in
    bn_bit_set_lemma b2 x;
    assert (bn_v b2' == pow2 x);
    bn_is_less_lemma b b2' end


val bn_gt_pow2: #len:size_nat -> b:lbignum len -> x:size_nat -> bool
let bn_gt_pow2 #len b x =
  if x >= 64 * len then false
  else begin
    let b2 = create len (u64 0) in
    let b2 = bn_bit_set b2 x in
    bn_is_less b2 b end

val bn_gt_pow2_lemma: #len:size_nat -> b:lbignum len -> x:size_nat -> Lemma
  (bn_gt_pow2 #len b x == (pow2 x < bn_v b))
let bn_gt_pow2_lemma #len b x =
  bn_eval_bound #len b len;
  assert (bn_v b < pow2 (64 * len));
  if x >= 64 * len then
    Math.Lemmas.pow2_le_compat x (64 * len)
  else begin
    let b2 = create len (u64 0) in
    bn_eval_zeroes len len;
    assert (bn_v b2 = 0);
    //assert (bn_v b2 < pow2 x);
    let b2' = bn_bit_set b2 x in
    bn_bit_set_lemma b2 x;
    assert (bn_v b2' == pow2 x);
    bn_is_less_lemma b2' b end
