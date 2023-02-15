module Hacl.Spec.Bignum.Squaring

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum.Base
open Hacl.Spec.Lib

module SM = Hacl.Spec.Bignum.Multiplication
module SA = Hacl.Spec.Bignum.Addition

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val bn_sqr_diag_f:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> i:nat{i < aLen}
  -> acc:lbignum t (aLen + aLen) ->
  lbignum t (aLen + aLen)

let bn_sqr_diag_f #t #aLen a i acc =
  let (hi, lo) = mul_wide a.[i] a.[i] in
  let acc = acc.[2 * i] <- lo in
  let acc = acc.[2 * i + 1] <- hi in
  acc


val bn_sqr_diag:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen ->
  lbignum t (aLen + aLen)

let bn_sqr_diag #t #aLen a =
  let acc0 = create (aLen + aLen) (uint #t 0) in
  repeati aLen (bn_sqr_diag_f a) acc0


val bn_sqr_f:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> j:nat{j < aLen}
  -> acc:lbignum t (aLen + aLen) ->
  lbignum t (aLen + aLen)

let bn_sqr_f #t #aLen a j acc =
  let c, acc = SM.bn_mul1_lshift_add (sub a 0 j) a.[j] j acc in
  acc.[j + j] <- c


val bn_sqr: #t:limb_t -> #aLen:size_nat{aLen + aLen <= max_size_t} -> a:lbignum t aLen -> lbignum t (aLen + aLen)
let bn_sqr #t #aLen a =
  let res = create (aLen + aLen) (uint #t 0) in
  let res = repeati aLen (bn_sqr_f a) res in
  let c, res = Hacl.Spec.Bignum.Addition.bn_add res res in
  let tmp = bn_sqr_diag a in
  let c, res = Hacl.Spec.Bignum.Addition.bn_add res tmp in
  res


val bn_sqr_diag_f_lemma:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> i:nat{i < aLen}
  -> acc:lbignum t (aLen + aLen) ->
  Lemma (let (hi, lo) = mul_wide a.[i] a.[i] in
    let res = bn_sqr_diag_f a i acc in
    res.[2 * i] == lo /\ res.[2 * i + 1] == hi /\
    (forall (i0:nat{i0 < aLen /\ i0 <> i}).
      acc.[2 * i0] == res.[2 * i0] /\
      acc.[2 * i0 + 1] == res.[2 * i0 + 1]))

let bn_sqr_diag_f_lemma #t #aLen a i acc =
  let (hi, lo) = mul_wide a.[i] a.[i] in
  let res1 = acc.[2 * i] <- lo in
  let res = res1.[2 * i + 1] <- hi in

  let aux (i0:nat{i0 < aLen + aLen /\ i0 <> 2 * i /\ i0 <> 2 * i + 1}) :
    Lemma (acc.[i0] == res.[i0]) = () in

  let aux2 (i0:nat{i0 < aLen /\ i0 <> i}) :
    Lemma (acc.[2 * i0] == res.[2 * i0] /\ acc.[2 * i0 + 1] == res.[2 * i0 + 1]) =
    aux (2 * i0);
    //assert (acc.[2 * i0] == res.[2 * i0]);
    aux (2 * i0 + 1);
    //assert (acc.[2 * i0 + 1] == res.[2 * i0 + 1]);
    () in

  Classical.forall_intro aux2


val bn_sqr_diag_inductive:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> k:nat{k <= aLen} ->
  Pure (lbignum t (aLen + aLen))
  (requires True)
  (ensures fun res ->
    (let acc0 = create (aLen + aLen) (uint #t 0) in
    res == repeati k (bn_sqr_diag_f a) acc0 /\
    (forall (i:nat{i < k}).
      let (hi, lo) = mul_wide a.[i] a.[i] in
      Seq.index res (2 * i) == lo /\
      Seq.index res (2 * i + 1) == hi) /\
    (forall (i:nat{k <= i /\ i < aLen}).
      Seq.index res (2 * i) == Seq.index acc0 (2 * i) /\
      Seq.index res (2 * i + 1) == Seq.index acc0 (2 * i + 1))))

let bn_sqr_diag_inductive #t #aLen a k =
  let acc0 = create (aLen + aLen) (uint #t 0) in

  eq_repeati0 k (bn_sqr_diag_f a) acc0;
  repeati_inductive k
  (fun i acci ->
    acci == repeati i (bn_sqr_diag_f a) acc0 /\
    (forall (i0:nat{i0 < i}).
      let (hi, lo) = mul_wide a.[i0] a.[i0] in
      Seq.index acci (2 * i0) == lo /\
      Seq.index acci (2 * i0 + 1) == hi) /\
    (forall (i0:nat{i <= i0 /\ i0 < aLen}).
      Seq.index acci (2 * i0) == Seq.index acc0 (2 * i0) /\
      Seq.index acci (2 * i0 + 1) == Seq.index acc0 (2 * i0 + 1)))
  (fun i acci ->
    unfold_repeati k (bn_sqr_diag_f a) acc0 i;
    let acc = bn_sqr_diag_f a i acci in
    bn_sqr_diag_f_lemma #t #aLen a i acci;
    acc)
  acc0


val bn_sqr_diag_lemma:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> k:nat{k <= aLen} ->
  Lemma (let acc0 = create (aLen + aLen) (uint #t 0) in
   let acc : lbignum t (aLen + aLen) = repeati k (bn_sqr_diag_f a) acc0 in
  (forall (i:nat{i < k}).
    let (hi, lo) = mul_wide a.[i] a.[i] in
    Seq.index acc (2 * i) == lo /\
    Seq.index acc (2 * i + 1) == hi) /\
  (forall (i:nat{k <= i /\ i < aLen}).
    Seq.index acc (2 * i) == Seq.index acc0 (2 * i) /\
    Seq.index acc (2 * i + 1) == Seq.index acc0 (2 * i + 1)))

let bn_sqr_diag_lemma #t #aLen a k =
  let _ = bn_sqr_diag_inductive a k in ()


val bn_sqr_diag_eq:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> k:nat{k < aLen} ->
  Lemma (let acc0 = create (aLen + aLen) (uint #t 0) in
   let acc1 : lbignum t (aLen + aLen) = repeati k (bn_sqr_diag_f a) acc0 in
   let acc2 : lbignum t (aLen + aLen) = repeati (k + 1) (bn_sqr_diag_f a) acc0 in
   slice acc1 0 (2 * k) == slice acc2 0 (2 * k))

let bn_sqr_diag_eq #t #aLen a k =
  let acc0 = create (aLen + aLen) (uint #t 0) in
  let acc1 : lbignum t (aLen + aLen) = repeati k (bn_sqr_diag_f a) acc0 in
  let acc2 : lbignum t (aLen + aLen) = repeati (k + 1) (bn_sqr_diag_f a) acc0 in

  let aux (i:nat{i < 2 * k}) : Lemma (Seq.index acc1 i == Seq.index acc2 i) =
    let i2 = i / 2 in
    bn_sqr_diag_lemma a k;
    bn_sqr_diag_lemma a (k + 1);
    assert
     (Seq.index acc1 (2 * i2) == Seq.index acc2 (2 * i2) /\
      Seq.index acc1 (2 * i2 + 1) == Seq.index acc2 (2 * i2 + 1));
    Math.Lemmas.euclidean_division_definition i 2;
    assert (Seq.index acc1 i == Seq.index acc2 i) in

  Classical.forall_intro aux;
  eq_intro (slice acc1 0 (2 * k)) (slice acc2 0 (2 * k))


val bn_sqr_diag_loop_step:
    #t:limb_t
  -> #aLen:size_pos{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> i:pos{i <= aLen} ->
  Lemma (let acc0 = create (aLen + aLen) (uint #t 0) in
   let acc1 : lbignum t (aLen + aLen) = repeati i (bn_sqr_diag_f a) acc0 in
   let acc2 : lbignum t (aLen + aLen) = repeati (i - 1) (bn_sqr_diag_f a) acc0 in
   eval_ (aLen + aLen) acc1 (i + i) ==
   eval_ (aLen + aLen) acc2 (i + i - 2) + v a.[i - 1] * v a.[i - 1] * pow2 (bits t * (i + i - 2)))

let bn_sqr_diag_loop_step #t #aLen a i =
  let pbits = bits t in
  let acc0 = create (aLen + aLen) (uint #t 0) in
  let acc1 : lbignum t (aLen + aLen) = repeati i (bn_sqr_diag_f a) acc0 in
  let acc2 : lbignum t (aLen + aLen) = repeati (i - 1) (bn_sqr_diag_f a) acc0 in

  bn_eval_unfold_i acc1 (i + i);
  bn_eval_unfold_i acc1 (i + i - 1);
  //assert (eval_ (aLen + aLen) acc1 (i + i) ==
    //eval_ (aLen + aLen) acc1 (i + i - 2) + v acc1.[i + i - 2] * (pow2 (p * (i + i - 2))) + v acc1.[i + i - 1] * pow2 (p * (i + i - 1)));

  calc (==) {
    v acc1.[i + i - 2] * pow2 (pbits * (i + i - 2)) + v acc1.[i + i - 1] * pow2 (pbits * (i + i - 1));
    (==) { Math.Lemmas.pow2_plus (pbits * (i + i - 2)) pbits }
    v acc1.[i + i - 2] * pow2 (pbits * (i + i - 2)) + v acc1.[i + i - 1] * (pow2 (pbits * (i + i - 2)) * pow2 pbits);
    (==) { Math.Lemmas.paren_mul_right (v acc1.[i + i - 1]) (pow2 pbits) (pow2 (pbits * (i + i - 2))) }
    v acc1.[i + i - 2] * pow2 (pbits * (i + i - 2)) + (v acc1.[i + i - 1] * pow2 pbits) * pow2 (pbits * (i + i - 2));
    (==) { Math.Lemmas.distributivity_add_left (v acc1.[i + i - 2]) (v acc1.[i + i - 1] * pow2 pbits) (pow2 (pbits * (i + i - 2))) }
    (v acc1.[i + i - 2] + v acc1.[i + i - 1] * pow2 pbits) * pow2 (pbits * (i + i - 2));
    (==) { bn_sqr_diag_lemma a i }
    v a.[i - 1] * v a.[i - 1] * pow2 (pbits * (i + i - 2));
  };

  bn_sqr_diag_eq a (i - 1);
  bn_eval_extensionality_j acc1 acc2 (i + i - 2);

  assert (eval_ (aLen + aLen) acc1 (i + i) ==
    eval_ (aLen + aLen) acc2 (i + i - 2) + v a.[i - 1] * v a.[i - 1] * (pow2 (pbits * (i + i - 2))))


val bn_sqr_f_lemma:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> j:size_nat{j < aLen}
  -> acc:lbignum t (aLen + aLen)
  -> i:nat{j + j < i /\ i < aLen + aLen} ->
  Lemma (let res = bn_sqr_f a j acc in
   eval_ (aLen + aLen) res (j + j + 1) ==
   eval_ (aLen + aLen) acc (j + j) + eval_ aLen a j * v a.[j] * pow2 (bits t * j) /\
   Seq.index res i == Seq.index acc i)

let bn_sqr_f_lemma #t #aLen a j acc i =
  let resLen = aLen + aLen in

  let c, acc' = SM.bn_mul1_add_in_place #t #j (sub a 0 j) a.[j] (sub acc j j) in
  let acc1 = update_sub acc j j acc' in
  assert (index acc1 i == index acc i);
  let res = acc1.[j + j] <- c in
  assert (index res i == index acc i);

  SM.bn_mul1_lshift_add_lemma #t #j #resLen (sub a 0 j) a.[j] j acc;
  bn_eval_extensionality_j acc1 res (j + j);
  bn_eval_unfold_i res (j + j + 1);
  bn_eval_extensionality_j a (sub a 0 j) j


val bn_sqr_inductive:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> k:nat{k <= aLen} ->
  Pure (lbignum t (aLen + aLen))
  (requires True)
  (ensures fun res ->
    (let acc0 = create (aLen + aLen) (uint #t 0) in
    res == repeati k (bn_sqr_f a) acc0 /\
    (forall (i:nat{k + k < i /\ i < aLen + aLen}). Seq.index res i == Seq.index acc0 i)))

let bn_sqr_inductive #t #aLen a k =
  let acc0 = create (aLen + aLen) (uint #t 0) in
  eq_repeati0 k (bn_sqr_f a) acc0;
  repeati_inductive #(lbignum t (aLen + aLen)) k
  (fun i acci ->
    acci == repeati i (bn_sqr_f a) acc0 /\
    (forall (i0:nat{i + i < i0 /\ i0 < aLen + aLen}). Seq.index acci i0 == Seq.index acc0 i0))
  (fun i acci ->
    unfold_repeati k (bn_sqr_f a) acc0 i;
    let acc1 = bn_sqr_f a i acci in
    assert (acc1 == repeati (i + 1) (bn_sqr_f a) acc0);
    Classical.forall_intro (bn_sqr_f_lemma a i acci);
    assert (forall (i0:nat{i + i + 2 < i0 /\ i0 < aLen + aLen}). Seq.index acc1 i0 == Seq.index acc0 i0);
    acc1)
  acc0


val bn_sqr_tail:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> k:nat{k <= aLen} ->
  Lemma (let acc0 = create (aLen + aLen) (uint #t 0) in
   let acc : lbignum t (aLen + aLen) = repeati k (bn_sqr_f a) acc0 in
   (forall (i:nat{k + k < i /\ i < aLen + aLen}). Seq.index acc i == uint #t 0))

let bn_sqr_tail #t #aLen a k =
  let _ = bn_sqr_inductive a k in ()


val square_of_sum: a:nat -> b:nat -> Lemma ((a + b) * (a + b) == a * a + 2 * a * b + b * b)
let square_of_sum a b = ()


val bn_eval_square:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> i:pos{i <= aLen} ->
  Lemma (eval_ aLen a i * eval_ aLen a i == eval_ aLen a (i - 1) * eval_ aLen a (i - 1) +
    2 * eval_ aLen a (i - 1) * v a.[i - 1] * pow2 (bits t * (i - 1)) + v a.[i - 1] * v a.[i - 1] * pow2 (bits t * (i + i - 2)))

let bn_eval_square #t #aLen a i =
  let e1 = eval_ aLen a (i - 1) in
  let p1 = pow2 (bits t * (i - 1)) in
  let p2 = pow2 (bits t * (i + i - 2)) in

  calc (==) {
    eval_ aLen a i * eval_ aLen a i;
    (==) { bn_eval_unfold_i a i }
    (e1 + v a.[i - 1] * p1) * (e1 + v a.[i - 1] * p1);
    (==) { square_of_sum e1 (v a.[i - 1] * p1) }
    e1 * e1 + 2 * e1 * (v a.[i - 1] * p1) + (v a.[i - 1] * p1) * (v a.[i - 1] * p1);
    (==) { Math.Lemmas.paren_mul_right (v a.[i - 1]) p1 (v a.[i - 1] * p1); Math.Lemmas.paren_mul_right p1 p1 (v a.[i - 1]) }
    e1 * e1 + 2 * e1 * (v a.[i - 1] * p1) + v a.[i - 1] * (p1 * p1 * v a.[i - 1]);
    (==) { Math.Lemmas.pow2_plus (bits t * (i - 1)) (bits t * (i - 1)) }
    e1 * e1 + 2 * e1 * (v a.[i - 1] * p1) + v a.[i - 1] * (p2 * v a.[i - 1]);
    (==) { Math.Lemmas.paren_mul_right (v a.[i - 1]) (v a.[i - 1]) p2 }
    e1 * e1 + 2 * e1 * (v a.[i - 1] * p1) + v a.[i - 1] * v a.[i - 1] * p2;
    (==) { Math.Lemmas.paren_mul_right (2 * e1) (v a.[i - 1]) p1 }
    e1 * e1 + 2 * e1 * v a.[i - 1] * p1 + v a.[i - 1] * v a.[i - 1] * p2;
    }


val bn_sqr_loop_lemma:
    #t:limb_t
  -> #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum t aLen
  -> i:nat{i <= aLen} ->
  Lemma (let resLen = aLen + aLen in
   let bn_zero = create (aLen + aLen) (uint #t 0) in
   let acc : lbignum t (aLen + aLen) = repeati i (bn_sqr_f a) bn_zero in
   let tmp : lbignum t (aLen + aLen) = repeati i (bn_sqr_diag_f a) bn_zero in
   2 * eval_ resLen acc (i + i) + eval_ resLen tmp (i + i) == eval_ aLen a i * eval_ aLen a i)

let rec bn_sqr_loop_lemma #t #aLen a i =
  let pbits = bits t in
  let resLen = aLen + aLen in
  let bn_zero = create (aLen + aLen) (uint #t 0) in
  let acc : lbignum t (aLen + aLen) = repeati i (bn_sqr_f a) bn_zero in
  let tmp : lbignum t (aLen + aLen) = repeati i (bn_sqr_diag_f a) bn_zero in

  if i = 0 then begin
    bn_eval0 acc;
    bn_eval0 tmp;
    bn_eval0 a end
  else begin
    let p1 = pow2 (pbits * (i + i - 1)) in
    let p2 = pow2 (pbits * (i + i - 2)) in
    let p3 = pow2 (pbits * (i - 1)) in
    let acc1 : lbignum t (aLen + aLen) = repeati (i - 1) (bn_sqr_f a) bn_zero in
    let tmp1 : lbignum t (aLen + aLen) = repeati (i - 1) (bn_sqr_diag_f a) bn_zero in

    unfold_repeati i (bn_sqr_f a) bn_zero (i - 1);
    assert (acc == bn_sqr_f a (i - 1) acc1);

    bn_sqr_f_lemma a (i - 1) acc1 (i + i - 1);
    assert (acc.[i + i - 1] == acc1.[i + i - 1]);
    bn_sqr_tail a (i - 1);
    assert (acc.[i + i - 1] == uint #t 0);

    calc (==) {
      2 * eval_ resLen acc (i + i) + eval_ resLen tmp (i + i);
      (==) { bn_sqr_diag_loop_step a i }
      2 * eval_ resLen acc (i + i) + eval_ resLen tmp1 (i + i - 2) + v a.[i - 1] * v a.[i - 1] * p2;
      (==) { bn_eval_unfold_i acc (i + i) }
      2 * (eval_ resLen acc (i + i - 1) + v acc.[i + i - 1] * p1) +
      eval_ (aLen + aLen) tmp1 (i + i - 2) + v a.[i - 1] * v a.[i - 1] * p2;
      (==) { Classical.forall_intro (bn_sqr_f_lemma a (i - 1) acc1) }
      2 * (eval_ resLen acc1 (i + i - 2) + eval_ aLen a (i - 1) * v a.[i - 1] * p3) +
      eval_ (aLen + aLen) tmp1 (i + i - 2) + v a.[i - 1] * v a.[i - 1] * p2;
      (==) { Math.Lemmas.distributivity_add_right 2 (eval_ resLen acc1 (i + i - 2)) (eval_ aLen a (i - 1) * v a.[i - 1] * p3) }
      2 * eval_ resLen acc1 (i + i - 2) + 2 * eval_ aLen a (i - 1) * v a.[i - 1] * p3 +
      eval_ (aLen + aLen) tmp1 (i + i - 2) + v a.[i - 1] * v a.[i - 1] * p2;
      (==) { bn_sqr_loop_lemma a (i - 1) }
      eval_ aLen a (i - 1) * eval_ aLen a (i - 1) + 2 * eval_ aLen a (i - 1) * v a.[i - 1] * p3 + v a.[i - 1] * v a.[i - 1] * p2;
      (==) { bn_eval_square a i }
      eval_ aLen a i * eval_ aLen a i;
    }; () end


val bn_sqr_lemma_eval: #t:limb_t -> #aLen:size_nat{aLen + aLen <= max_size_t} -> a:lbignum t aLen ->
  Lemma (bn_v (bn_sqr a) == bn_v a * bn_v a)

let bn_sqr_lemma_eval #t #aLen a =
  let pbits = bits t in
  let resLen = aLen + aLen in
  let res0 = create (aLen + aLen) (uint #t 0) in
  let res1 = repeati aLen (bn_sqr_f a) res0 in
  let c0, res2 = Hacl.Spec.Bignum.Addition.bn_add res1 res1 in
  Hacl.Spec.Bignum.Addition.bn_add_lemma res1 res1;
  let tmp = bn_sqr_diag a in
  let c1, res3 = Hacl.Spec.Bignum.Addition.bn_add res2 tmp in
  Hacl.Spec.Bignum.Addition.bn_add_lemma res2 tmp;
  assert ((v c0 + v c1) * pow2 (pbits * resLen) + bn_v res3 == 2 * bn_v res1 + bn_v tmp);
  bn_sqr_loop_lemma a aLen;
  assert (2 * bn_v res1 + bn_v tmp == bn_v a * bn_v a);
  bn_eval_bound a aLen;
  Math.Lemmas.lemma_mult_lt_sqr (bn_v a) (bn_v a) (pow2 (pbits * aLen));
  Math.Lemmas.pow2_plus (pbits * aLen) (pbits * aLen);
  assert (bn_v a * bn_v a < pow2 (pbits * resLen));
  bn_eval_bound res3 resLen;
  assert ((v c0 + v c1) = 0)


val bn_sqr_lemma: #t:limb_t -> #aLen:size_nat{aLen + aLen <= max_size_t} -> a:lbignum t aLen ->
  Lemma (bn_sqr a == SM.bn_mul a a /\ bn_v (bn_sqr a) == bn_v a * bn_v a)

let bn_sqr_lemma #t #aLen a =
  let res = bn_sqr a in
  bn_sqr_lemma_eval a;
  assert (bn_v res == bn_v a * bn_v a);
  let res' = SM.bn_mul a a in
  SM.bn_mul_lemma a a;
  assert (bn_v res' == bn_v a * bn_v a);
  bn_eval_inj (aLen + aLen) res res';
  assert (bn_sqr a == SM.bn_mul a a)
