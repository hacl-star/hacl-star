module Hacl.Spec.Bignum.Multiplication

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Addition


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val bn_mul_by_limb_add_f:
    #aLen:size_nat
  -> a:lbignum aLen
  -> l:uint64
  -> acc:lbignum aLen
  -> i:size_nat{i < aLen}
  -> c:uint64 ->
  uint64 & uint64 // carry & out

let bn_mul_by_limb_add_f #aLen a l acc i c =
  mul_carry_add_u64 a.[i] l c acc.[i]


val bn_mul_by_limb_add:
    #aLen:size_nat
  -> a:lbignum aLen
  -> l:uint64
  -> acc:lbignum aLen ->
  uint64 & lbignum aLen

let bn_mul_by_limb_add #aLen a l acc =
  generate_elems aLen aLen (bn_mul_by_limb_add_f a l acc) (u64 0)


val bn_mul_:
    #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> j:size_nat{j < bLen}
  -> res:lbignum (aLen + bLen) ->
  lbignum (aLen + bLen)

let bn_mul_ #aLen #bLen a b j res =
  let res' = sub res j aLen in
  let c, res' = bn_mul_by_limb_add #aLen a b.[j] res' in
  let res = update_sub res j aLen res' in
  res.[aLen + j] <- c


val bn_mul:
    #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum aLen
  -> b:lbignum bLen ->
  lbignum (aLen + bLen)

let bn_mul #aLen #bLen a b =
  let res = create (aLen + bLen) (u64 0) in
  repeati bLen (bn_mul_ #aLen #bLen a b) res



///
///  Lemma (let (c, res1) = bn_mul_by_limb_add #aLen a l res in
///    v c * pow2 (64 * aLen) + bn_v res1 == bn_v res + bn_v a * v l)
///


val bn_mul_by_limb_add_lemma_loop_step:
    #aLen:size_nat
  -> a:lbignum aLen
  -> l:uint64
  -> acc:lbignum aLen
  -> i:pos{i <= aLen}
  -> c1_res1:generate_elem_a uint64 uint64 aLen (i - 1) -> Lemma
  (requires
   (let (c1, res1) = c1_res1 in
    v c1 * pow2 (64 * (i - 1)) + bn_v #(i - 1) res1 == eval_ aLen acc (i - 1) + eval_ aLen a (i - 1) * v l))
  (ensures
   (let (c1, res1) = c1_res1 in
    let (c, res) = generate_elem_f #uint64 #uint64 aLen (bn_mul_by_limb_add_f a l acc) (i - 1) (c1, res1) in
    v c * pow2 (64 * i) + bn_v #i res == eval_ aLen acc i + eval_ aLen a i * v l))

let bn_mul_by_limb_add_lemma_loop_step #aLen a l acc i (c1, res1) =
  let (c, res) = generate_elem_f #uint64 #uint64 aLen (bn_mul_by_limb_add_f a l acc) (i - 1) (c1, res1) in
  let c, e = mul_carry_add_u64 a.[i - 1] l c1 acc.[i - 1] in
  assert (v e + v c * pow2 64 == v a.[i - 1] * v l + v c1 + v acc.[i - 1]);

  calc (==) {
    v c * pow2 (64 * i) + bn_v #i res;
    (==) { bn_eval_snoc #(i - 1) res1 e }
    v c * pow2 (64 * i) + bn_v #(i - 1) res1 + v e * pow2 (64 * (i - 1));
    (==) { }
    v c * pow2 (64 * i) + eval_ aLen acc (i - 1) + eval_ aLen a (i - 1) * v l -
      (v e + v c * pow2 64 - v a.[i - 1] * v l - v acc.[i - 1]) * pow2 (64 * (i - 1)) + v e * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.distributivity_add_left (v e) (v c * pow2 64 - v a.[i - 1] * v l - v acc.[i - 1]) (pow2 (64 * (i - 1))) }
    v c * pow2 (64 * i) + eval_ aLen acc (i - 1) + eval_ aLen a (i - 1) * v l - (v c * pow2 64 - v a.[i - 1] * v l - v acc.[i - 1]) * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v c * pow2 64) (v a.[i - 1] * v l + v acc.[i - 1]) (pow2 (64 * (i - 1))) }
    v c * pow2 (64 * i) + eval_ aLen acc (i - 1) + eval_ aLen a (i - 1) * v l - (v c * pow2 64) * pow2 (64 * (i - 1)) +
      (v a.[i - 1] * v l + v acc.[i - 1]) * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.paren_mul_right (v c) (pow2 64) (pow2 (64 * (i - 1))); Math.Lemmas.pow2_plus 64 (64 * (i - 1)) }
    eval_ aLen acc (i - 1) + eval_ aLen a (i - 1) * v l + (v a.[i - 1] * v l + v acc.[i - 1]) * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.distributivity_add_left (v a.[i - 1] * v l) (v acc.[i - 1]) (pow2 (64 * (i - 1))) }
    eval_ aLen acc (i - 1) + eval_ aLen a (i - 1) * v l + v a.[i - 1] * v l * pow2 (64 * (i - 1)) + v acc.[i - 1] * pow2 (64 * (i - 1));
    (==) { bn_eval_unfold_i #aLen acc i }
    eval_ aLen acc i + eval_ aLen a (i - 1) * v l + v a.[i - 1] * v l * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.paren_mul_right (v a.[i - 1]) (v l) (pow2 (64 * (i - 1))) }
    eval_ aLen acc i + eval_ aLen a (i - 1) * v l + v a.[i - 1] * (pow2 (64 * (i - 1)) * v l);
    (==) { Math.Lemmas.paren_mul_right (v a.[i - 1]) (pow2 (64 * (i - 1))) (v l) }
    eval_ aLen acc i + eval_ aLen a (i - 1) * v l + v a.[i - 1] * pow2 (64 * (i - 1)) * v l;
    (==) { Math.Lemmas.distributivity_add_left (eval_ aLen a (i - 1)) (v a.[i - 1] * pow2 (64 * (i - 1))) (v l) }
    eval_ aLen acc i + (eval_ aLen a (i - 1) + v a.[i - 1] * pow2 (64 * (i - 1))) * v l;
    (==) { bn_eval_unfold_i #aLen a i }
    eval_ aLen acc i + eval_ aLen a i * v l;
  };
  assert (v c * pow2 (64 * i) + bn_v #i res == eval_ aLen acc i + eval_ aLen a i * v l)


val bn_mul_by_limb_add_lemma_loop:
    #aLen:size_nat
  -> a:lbignum aLen
  -> l:uint64
  -> acc:lbignum aLen
  -> i:nat{i <= aLen} -> Lemma
  (let (c, res) : generate_elem_a uint64 uint64 aLen i = generate_elems aLen i (bn_mul_by_limb_add_f a l acc) (u64 0) in
   v c * pow2 (64 * i) + bn_v #i res == eval_ aLen acc i + eval_ aLen a i * v l)

let rec bn_mul_by_limb_add_lemma_loop #aLen a l acc i =
  let (c, res) : generate_elem_a uint64 uint64 aLen i = generate_elems aLen i (bn_mul_by_limb_add_f a l acc) (u64 0) in
  if i = 0 then begin
    eq_generate_elems0 #uint64 #uint64 aLen i (bn_mul_by_limb_add_f a l acc) (u64 0);
    assert (c == u64 0 /\ res == Seq.empty);
    bn_eval0 #0 res;
    assert_norm (pow2 0 = 1);
    bn_eval0 a;
    bn_eval0 acc;
    () end
  else begin
    let (c1, res1) : generate_elem_a uint64 uint64 aLen (i - 1) = generate_elems aLen (i - 1) (bn_mul_by_limb_add_f a l acc) (u64 0) in
    generate_elems_unfold #uint64 #uint64 aLen i (bn_mul_by_limb_add_f a l acc) (u64 0) (i - 1);
    assert (generate_elems #uint64 #uint64 aLen i (bn_mul_by_limb_add_f a l acc) (u64 0) ==
      generate_elem_f aLen (bn_mul_by_limb_add_f a l acc) (i - 1) (generate_elems #uint64 #uint64 aLen (i - 1) (bn_mul_by_limb_add_f a l acc) (u64 0)));
    assert ((c, res) == generate_elem_f #uint64 #uint64 aLen (bn_mul_by_limb_add_f a l acc) (i - 1) (c1, res1));
    bn_mul_by_limb_add_lemma_loop #aLen a l acc (i - 1);
    assert (v c1 * pow2 (64 * (i - 1)) + bn_v #(i - 1) res1 == eval_ aLen acc (i - 1) + eval_ aLen a (i - 1) * v l);
    bn_mul_by_limb_add_lemma_loop_step #aLen a l acc i (c1, res1);
    assert (v c * pow2 (64 * i) + bn_v #i res == eval_ aLen acc i + eval_ aLen a i * v l);
    () end


val bn_mul_by_limb_add_lemma:
    #aLen:size_nat
  -> a:lbignum aLen
  -> l:uint64
  -> acc:lbignum aLen -> Lemma
  (let (c, res) = bn_mul_by_limb_add #aLen a l acc in
   v c * pow2 (64 * aLen) + bn_v res == bn_v acc + bn_v a * v l)

let bn_mul_by_limb_add_lemma #aLen a l acc =
  let (c, res) = bn_mul_by_limb_add #aLen a l acc in
  bn_mul_by_limb_add_lemma_loop #aLen a l acc aLen
