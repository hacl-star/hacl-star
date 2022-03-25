module Hacl.Spec.Bignum.Multiplication

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum.Base
open Hacl.Spec.Lib


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val bn_mul1_f:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> l:limb t
  -> i:size_nat{i < aLen}
  -> c:limb t ->
  limb t & limb t // carry & out

let bn_mul1_f #t #aLen a l i c =
  mul_wide_add a.[i] l c


val bn_mul1:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> l:limb t ->
  limb t & lbignum t aLen

let bn_mul1 #t #aLen a l =
  generate_elems aLen aLen (bn_mul1_f a l) (uint #t 0)


val bn_mul1_add_in_place_f:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> l:limb t
  -> acc:lbignum t aLen
  -> i:size_nat{i < aLen}
  -> c:limb t ->
  limb t & limb t // carry & out

let bn_mul1_add_in_place_f #t #aLen a l acc i c =
  mul_wide_add2 a.[i] l c acc.[i]


val bn_mul1_add_in_place:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> l:limb t
  -> acc:lbignum t aLen ->
  limb t & lbignum t aLen

let bn_mul1_add_in_place #t #aLen a l acc =
  generate_elems aLen aLen (bn_mul1_add_in_place_f a l acc) (uint #t 0)


val bn_mul1_lshift_add:
    #t:limb_t
  -> #aLen:size_nat
  -> #resLen:size_nat
  -> a:lbignum t aLen
  -> b_j:limb t
  -> j:size_nat{j + aLen <= resLen}
  -> res:lbignum t resLen ->
  limb t & lbignum t resLen

let bn_mul1_lshift_add #t #aLen #resLen a b_j j res =
  let res' = sub res j aLen in
  let c, res' = bn_mul1_add_in_place a b_j res' in
  let res = update_sub res j aLen res' in
  c, res


val bn_mul_:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t bLen
  -> j:size_nat{j < bLen}
  -> res:lbignum t (aLen + bLen) ->
  lbignum t (aLen + bLen)

let bn_mul_ #t #aLen #bLen a b j res =
  let c, res = bn_mul1_lshift_add a b.[j] j res in
  res.[aLen + j] <- c


val bn_mul:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t bLen ->
  lbignum t (aLen + bLen)

let bn_mul #t #aLen #bLen a b =
  let res = create (aLen + bLen) (uint #t 0) in
  repeati bLen (bn_mul_ a b) res


val bn_mul_unroll1:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_pos{aLen + bLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t bLen ->
  lbignum t (aLen + bLen)

let bn_mul_unroll1 #t #aLen #bLen a b =
  let res = create (aLen + bLen) (uint #t 0) in

  let c, ab0 = bn_mul1 a b.[0] in
  let res = update_sub res 0 aLen ab0 in
  let res = res.[aLen] <- c in

  repeat_right 1 bLen (fixed_a (lbignum t (aLen + bLen))) (bn_mul_ a b) res


val bn_mul1_lemma_loop_step:
     #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> l:limb t
  -> i:pos{i <= aLen}
  -> c1_res1:generate_elem_a (limb t) (limb t) aLen (i - 1) -> Lemma
  (requires
   (let (c1, res1) = c1_res1 in
    v c1 * pow2 (bits t * (i - 1)) + bn_v #t #(i - 1) res1 == eval_ aLen a (i - 1) * v l))
  (ensures
   (let (c1, res1) = c1_res1 in
    let (c, res) = generate_elem_f aLen (bn_mul1_f a l) (i - 1) (c1, res1) in
    v c * pow2 (bits t * i) + bn_v #t #i res == eval_ aLen a i * v l))

let bn_mul1_lemma_loop_step #t #aLen a l i (c1, res1) =
  let pbits = bits t in
  let b1 = pow2 (pbits * (i - 1)) in
  let b2 = pow2 (pbits * i) in

  let (c, res) = generate_elem_f aLen (bn_mul1_f a l) (i - 1) (c1, res1) in
  let c, e = mul_wide_add a.[i - 1] l c1 in
  assert (v e + v c * pow2 pbits == v a.[i - 1] * v l + v c1);

  calc (==) {
    v c * b2 + bn_v #t #i res;
    (==) { bn_eval_snoc #t #(i - 1) res1 e }
    v c * b2 + bn_v #t #(i - 1) res1 + v e * b1;
    (==) { }
    v c * b2 + eval_ aLen a (i - 1) * v l -(v e + v c * pow2 pbits - v a.[i - 1] * v l) * b1 + v e * b1;
    (==) { Math.Lemmas.distributivity_add_left (v e) (v c * pow2 pbits - v a.[i - 1] * v l) b1 }
    v c * b2 + eval_ aLen a (i - 1) * v l - (v c * pow2 pbits - v a.[i - 1] * v l) * b1;
    (==) { Math.Lemmas.distributivity_sub_left (v c * pow2 pbits) (v a.[i - 1] * v l) b1 }
    v c * b2 + eval_ aLen a (i - 1) * v l - v c * pow2 pbits * b1 + v a.[i - 1] * v l * b1;
    (==) { Math.Lemmas.paren_mul_right (v c) (pow2 pbits) b1; Math.Lemmas.pow2_plus pbits (pbits * (i - 1)) }
    eval_ aLen a (i - 1) * v l + v a.[i - 1] * v l * b1;
    (==) { Math.Lemmas.paren_mul_right (v a.[i - 1]) (v l) b1 }
    eval_ aLen a (i - 1) * v l + v a.[i - 1] * (b1 * v l);
    (==) { Math.Lemmas.paren_mul_right (v a.[i - 1]) b1 (v l) }
    eval_ aLen a (i - 1) * v l + v a.[i - 1] * b1 * v l;
    (==) { Math.Lemmas.distributivity_add_left (eval_ aLen a (i - 1)) (v a.[i - 1] * b1) (v l) }
    (eval_ aLen a (i - 1) + v a.[i - 1] * b1) * v l;
    (==) { bn_eval_unfold_i a i }
    eval_ aLen a i * v l;
  };
  assert (v c * b2 + bn_v #t #i res == eval_ aLen a i * v l)


val bn_mul1_lemma_loop:
     #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> l:limb t
  -> i:nat{i <= aLen} ->
  Lemma (let (c, res) : generate_elem_a (limb t) (limb t) aLen i = generate_elems aLen i (bn_mul1_f a l) (uint #t 0) in
   v c * pow2 (bits t * i) + bn_v #t #i res == eval_ aLen a i * v l)

let rec bn_mul1_lemma_loop #t #aLen a l i =
  let pbits = bits t in
  let (c, res) : generate_elem_a (limb t) (limb t) aLen i = generate_elems aLen i (bn_mul1_f a l) (uint #t 0) in
  if i = 0 then begin
    eq_generate_elems0 aLen i (bn_mul1_f a l) (uint #t 0);
    assert (c == uint #t 0 /\ res == Seq.empty);
    bn_eval0 #t #0 res;
    assert_norm (pow2 0 = 1);
    bn_eval0 a;
    () end
  else begin
    let (c1, res1) : generate_elem_a (limb t) (limb t) aLen (i - 1) = generate_elems aLen (i - 1) (bn_mul1_f a l) (uint #t 0) in
    generate_elems_unfold aLen i (bn_mul1_f a l) (uint #t 0) (i - 1);
    assert (generate_elems aLen i (bn_mul1_f a l) (uint #t 0) ==
      generate_elem_f aLen (bn_mul1_f a l) (i - 1) (generate_elems aLen (i - 1) (bn_mul1_f a l) (uint #t 0)));
    assert ((c, res) == generate_elem_f aLen (bn_mul1_f a l) (i - 1) (c1, res1));
    bn_mul1_lemma_loop a l (i - 1);
    assert (v c1 * pow2 (pbits * (i - 1)) + bn_v #t #(i - 1) res1 == eval_ aLen a (i - 1) * v l);
    bn_mul1_lemma_loop_step a l i (c1, res1);
    assert (v c * pow2 (pbits * i) + bn_v #t #i res == eval_ aLen a i * v l);
    () end


val bn_mul1_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> l:limb t ->
  Lemma (let (c, res) = bn_mul1 a l in
   v c * pow2 (bits t * aLen) + bn_v res == bn_v a * v l)

let bn_mul1_lemma #t #aLen a l =
  let (c, res) = bn_mul1 a l in
  bn_mul1_lemma_loop a l aLen


#push-options "--z3rlimit 150"
val bn_mul1_add_in_place_lemma_loop_step:
     #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> l:limb t
  -> acc:lbignum t aLen
  -> i:pos{i <= aLen}
  -> c1_res1:generate_elem_a (limb t) (limb t) aLen (i - 1) -> Lemma
  (requires
   (let (c1, res1) = c1_res1 in
    v c1 * pow2 (bits t * (i - 1)) + bn_v #t #(i - 1) res1 == eval_ aLen acc (i - 1) + eval_ aLen a (i - 1) * v l))
  (ensures
   (let (c1, res1) = c1_res1 in
    let (c, res) = generate_elem_f aLen (bn_mul1_add_in_place_f a l acc) (i - 1) (c1, res1) in
    v c * pow2 (bits t * i) + bn_v #t #i res == eval_ aLen acc i + eval_ aLen a i * v l))

let bn_mul1_add_in_place_lemma_loop_step #t #aLen a l acc i (c1, res1) =
  let pbits = bits t in
  let b1 = pow2 (pbits * (i - 1)) in
  let b2 = pow2 (pbits * i) in

  let (c, res) = generate_elem_f aLen (bn_mul1_add_in_place_f a l acc) (i - 1) (c1, res1) in
  let c, e = mul_wide_add2 a.[i - 1] l c1 acc.[i - 1] in
  assert (v e + v c * pow2 pbits == v a.[i - 1] * v l + v c1 + v acc.[i - 1]);

  calc (==) {
    v c * b2 + bn_v #t #i res;
    (==) { bn_eval_snoc #t #(i - 1) res1 e }
    v c * b2 + bn_v #t #(i - 1) res1 + v e * b1;
    (==) { }
    v c * b2 + eval_ aLen acc (i - 1) + eval_ aLen a (i - 1) * v l -
      (v e + v c * pow2 pbits - v a.[i - 1] * v l - v acc.[i - 1]) * b1 + v e * b1;
    (==) { Math.Lemmas.distributivity_add_left (v e) (v c * pow2 pbits - v a.[i - 1] * v l - v acc.[i - 1]) b1 }
    v c * b2 + eval_ aLen acc (i - 1) + eval_ aLen a (i - 1) * v l - (v c * pow2 pbits - v a.[i - 1] * v l - v acc.[i - 1]) * b1;
    (==) { Math.Lemmas.distributivity_sub_left (v c * pow2 pbits) (v a.[i - 1] * v l + v acc.[i - 1]) b1 }
    v c * b2 + eval_ aLen acc (i - 1) + eval_ aLen a (i - 1) * v l - (v c * pow2 pbits) * b1 +
      (v a.[i - 1] * v l + v acc.[i - 1]) * b1;
    (==) { Math.Lemmas.paren_mul_right (v c) (pow2 pbits) b1; Math.Lemmas.pow2_plus pbits (pbits * (i - 1)) }
    eval_ aLen acc (i - 1) + eval_ aLen a (i - 1) * v l + (v a.[i - 1] * v l + v acc.[i - 1]) * b1;
    (==) { Math.Lemmas.distributivity_add_left (v a.[i - 1] * v l) (v acc.[i - 1]) b1 }
    eval_ aLen acc (i - 1) + eval_ aLen a (i - 1) * v l + v a.[i - 1] * v l * b1 + v acc.[i - 1] * b1;
    (==) { bn_eval_unfold_i acc i }
    eval_ aLen acc i + eval_ aLen a (i - 1) * v l + v a.[i - 1] * v l * b1;
    (==) { Math.Lemmas.paren_mul_right (v a.[i - 1]) (v l) b1 }
    eval_ aLen acc i + eval_ aLen a (i - 1) * v l + v a.[i - 1] * (b1 * v l);
    (==) { Math.Lemmas.paren_mul_right (v a.[i - 1]) b1 (v l) }
    eval_ aLen acc i + eval_ aLen a (i - 1) * v l + v a.[i - 1] * b1 * v l;
    (==) { Math.Lemmas.distributivity_add_left (eval_ aLen a (i - 1)) (v a.[i - 1] * b1) (v l) }
    eval_ aLen acc i + (eval_ aLen a (i - 1) + v a.[i - 1] * b1) * v l;
    (==) { bn_eval_unfold_i a i }
    eval_ aLen acc i + eval_ aLen a i * v l;
  };
  assert (v c * b2 + bn_v #t #i res == eval_ aLen acc i + eval_ aLen a i * v l)
#pop-options


val bn_mul1_add_in_place_lemma_loop:
     #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> l:limb t
  -> acc:lbignum t aLen
  -> i:nat{i <= aLen} ->
  Lemma (let (c, res) : generate_elem_a (limb t) (limb t) aLen i = generate_elems aLen i (bn_mul1_add_in_place_f a l acc) (uint #t 0) in
   v c * pow2 (bits t * i) + bn_v #t #i res == eval_ aLen acc i + eval_ aLen a i * v l)

let rec bn_mul1_add_in_place_lemma_loop #t #aLen a l acc i =
  let pbits = bits t in
  let (c, res) : generate_elem_a (limb t) (limb t) aLen i = generate_elems aLen i (bn_mul1_add_in_place_f a l acc) (uint #t 0) in
  if i = 0 then begin
    eq_generate_elems0 aLen i (bn_mul1_add_in_place_f a l acc) (uint #t 0);
    assert (c == uint #t 0 /\ res == Seq.empty);
    bn_eval0 #t #0 res;
    assert_norm (pow2 0 = 1);
    bn_eval0 a;
    bn_eval0 acc;
    () end
  else begin
    let (c1, res1) : generate_elem_a (limb t) (limb t) aLen (i - 1) = generate_elems aLen (i - 1) (bn_mul1_add_in_place_f a l acc) (uint #t 0) in
    generate_elems_unfold aLen i (bn_mul1_add_in_place_f a l acc) (uint #t 0) (i - 1);
    assert (generate_elems aLen i (bn_mul1_add_in_place_f a l acc) (uint #t 0) ==
      generate_elem_f aLen (bn_mul1_add_in_place_f a l acc) (i - 1) (generate_elems aLen (i - 1) (bn_mul1_add_in_place_f a l acc) (uint #t 0)));
    assert ((c, res) == generate_elem_f aLen (bn_mul1_add_in_place_f a l acc) (i - 1) (c1, res1));
    bn_mul1_add_in_place_lemma_loop a l acc (i - 1);
    assert (v c1 * pow2 (pbits * (i - 1)) + bn_v #t #(i - 1) res1 == eval_ aLen acc (i - 1) + eval_ aLen a (i - 1) * v l);
    bn_mul1_add_in_place_lemma_loop_step a l acc i (c1, res1);
    assert (v c * pow2 (pbits * i) + bn_v #t #i res == eval_ aLen acc i + eval_ aLen a i * v l);
    () end


val bn_mul1_add_in_place_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> l:limb t
  -> acc:lbignum t aLen ->
  Lemma (let (c, res) = bn_mul1_add_in_place a l acc in
   v c * pow2 (bits t * aLen) + bn_v res == bn_v acc + bn_v a * v l)

let bn_mul1_add_in_place_lemma #t #aLen a l acc =
  let (c, res) = bn_mul1_add_in_place a l acc in
  bn_mul1_add_in_place_lemma_loop a l acc aLen


val bn_mul1_lshift_add_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> #resLen:size_nat
  -> a:lbignum t aLen
  -> b_j:limb t
  -> j:size_nat{j + aLen <= resLen}
  -> acc:lbignum t resLen ->
  Lemma (let (c, res) = bn_mul1_lshift_add a b_j j acc in
   v c * pow2 (bits t * (aLen + j)) + eval_ resLen res (aLen + j) ==
   eval_ resLen acc (aLen + j) + bn_v a * v b_j * pow2 (bits t * j) /\
   slice res (aLen + j) resLen == slice acc (aLen + j) resLen)

let bn_mul1_lshift_add_lemma #t #aLen #resLen a b_j j acc =
  let pbits = bits t in
  let res1 = sub acc j aLen in
  let c, res2 = bn_mul1_add_in_place a b_j res1 in
  bn_mul1_add_in_place_lemma a b_j res1;
  assert (v c * pow2 (pbits * aLen) + bn_v res2 == bn_v res1 + bn_v a * v b_j);
  let res = update_sub acc j aLen res2 in
  bn_eval_split_i (sub res 0 (j + aLen)) j;
  bn_eval_extensionality_j res (sub res 0 (j + aLen)) (j + aLen);
  assert (eval_ resLen res (j + aLen) == bn_v #t #j (sub res 0 j) + pow2 (pbits * j) * bn_v res2);
  eq_intro (sub res 0 j) (sub acc 0 j);
  assert (bn_v #t #j (sub res 0 j) == bn_v #t #j (sub acc 0 j));
  bn_eval_split_i (sub acc 0 (j + aLen)) j;
  bn_eval_extensionality_j acc (sub acc 0 (j + aLen)) (j + aLen);
  assert (eval_ resLen acc (j + aLen) == bn_v #t #j (sub acc 0 j) + pow2 (pbits * j) * bn_v res1);

  calc (==) {
    v c * pow2 (pbits * (aLen + j)) + eval_ resLen res (aLen + j);
    (==) { Math.Lemmas.pow2_plus (pbits * aLen) (pbits * j) }
    v c * (pow2 (pbits * aLen) * pow2 (pbits * j)) + eval_ resLen res (aLen + j);
    (==) { Math.Lemmas.paren_mul_right (v c) (pow2 (pbits * aLen)) (pow2 (pbits * j)) }
    v c * pow2 (pbits * aLen) * pow2 (pbits * j) + eval_ resLen res (aLen + j);
    (==) { }
    (bn_v res1 + bn_v a * v b_j - bn_v res2) * pow2 (pbits * j) + eval_ resLen res (aLen + j);
    (==) { }
    (bn_v res1 + bn_v a * v b_j - bn_v res2) * pow2 (pbits * j) + eval_ resLen acc (j + aLen) - pow2 (pbits * j) * bn_v res1 + pow2 (pbits * j) * bn_v res2;
    (==) { Math.Lemmas.distributivity_add_right (pow2 (pbits * j)) (bn_v res1) (bn_v a * v b_j - bn_v res2) }
    pow2 (pbits * j) * (bn_v a * v b_j - bn_v res2) + eval_ resLen acc (j + aLen) + pow2 (pbits * j) * bn_v res2;
    (==) { Math.Lemmas.distributivity_sub_right (pow2 (pbits * j)) (bn_v a * v b_j) (bn_v res2) }
    pow2 (pbits * j) * (bn_v a * v b_j) + eval_ resLen acc (j + aLen);
  };
  assert (v c * pow2 (pbits * (aLen + j)) + eval_ resLen res (aLen + j) ==
    eval_ resLen acc (aLen + j) + bn_v a * v b_j * pow2 (pbits * j));
  eq_intro (slice res (aLen + j) resLen) (slice acc (aLen + j) resLen)


val bn_mul_lemma_:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t bLen
  -> j:size_nat{j < bLen}
  -> acc:lbignum t (aLen + bLen) ->
  Lemma (let res = bn_mul_ a b j acc in
   v res.[aLen + j] * pow2 (bits t * (aLen + j)) + eval_ (aLen + bLen) res (aLen + j) ==
   eval_ (aLen + bLen) acc (aLen + j) + bn_v a * v b.[j] * pow2 (bits t * j) /\
   slice res (aLen + j + 1) (aLen + bLen) == slice acc (aLen + j + 1) (aLen + bLen))

let bn_mul_lemma_ #t #aLen #bLen a b j acc =
  let resLen = aLen + bLen in
  let c, res = bn_mul1_lshift_add a b.[j] j acc in
  bn_mul1_lshift_add_lemma a b.[j] j acc;

  let res1 = res.[aLen + j] <- c in
  bn_eval_extensionality_j res res1 (aLen + j);

  let lemma_aux (i:nat{aLen + j + 1 <= i /\ i < resLen}) : Lemma (index res1 i == index acc i) =
    assert (index res1 i == index res i);
    Seq.lemma_index_slice res (aLen + j) resLen (i - aLen - j);
    Seq.lemma_index_slice acc (aLen + j) resLen (i - aLen - j);
    assert (index res i == index acc i) in

  Classical.forall_intro lemma_aux;
  eq_intro (slice res1 (aLen + j + 1) resLen) (slice acc (aLen + j + 1) resLen)


val bn_mul_loop_lemma_step:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t bLen
  -> i:pos{i <= bLen}
  -> resi1:lbignum t (aLen + bLen) -> Lemma
  (requires eval_ (aLen + bLen) resi1 (aLen + i - 1) == bn_v a * eval_ bLen b (i - 1))
  (ensures
    (let resi = bn_mul_ a b (i - 1) resi1 in
    eval_ (aLen + bLen) resi (aLen + i) == bn_v a * eval_ bLen b i))

let bn_mul_loop_lemma_step #t #aLen #bLen a b i resi1 =
  let pbits = bits t in
  let resi = bn_mul_ a b (i - 1) resi1 in
  bn_mul_lemma_ a b (i - 1) resi1;
  assert
    (v resi.[aLen + i - 1] * pow2 (pbits * (aLen + i - 1)) + eval_ (aLen + bLen) resi (aLen + i - 1) ==
     eval_ (aLen + bLen) resi1 (aLen + i - 1) + bn_v a * v b.[i - 1] * (pow2 (pbits * (i - 1))));

  calc (==) {
    eval_ (aLen + bLen) resi (aLen + i);
    (==) { bn_eval_unfold_i resi (aLen + i) }
    eval_ (aLen + bLen) resi (aLen + i - 1) + v resi.[aLen + i - 1] * pow2 (pbits * (aLen + i - 1));
    (==) { }
    eval_ (aLen + bLen) resi1 (aLen + i - 1) + bn_v a * v b.[i - 1] * (pow2 (pbits * (i - 1)));
    (==) { }
    bn_v a * eval_ bLen b (i - 1) + bn_v a * v b.[i - 1] * (pow2 (pbits * (i - 1)));
    (==) { Math.Lemmas.paren_mul_right (bn_v a) (v b.[i - 1]) (pow2 (pbits * (i - 1))) }
    bn_v a * eval_ bLen b (i - 1) + bn_v a * (v b.[i - 1] * (pow2 (pbits * (i - 1))));
    (==) { Math.Lemmas.distributivity_add_right (bn_v a) (eval_ bLen b (i - 1)) (v b.[i - 1] * (pow2 (pbits * (i - 1)))) }
    bn_v a * (eval_ bLen b (i - 1) + v b.[i - 1] * (pow2 (pbits * (i - 1))));
    (==) { bn_eval_unfold_i b i }
    bn_v a * eval_ bLen b i;
  };
  assert (eval_ (aLen + bLen) resi (aLen + i) == bn_v a * eval_ bLen b i)


val bn_mul_loop_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t bLen
  -> i:nat{i <= bLen} ->
  Lemma (let res = create (aLen + bLen) (uint #t 0) in
   let resi = repeati i (bn_mul_ a b) res in
   eval_ (aLen + bLen) resi (aLen + i) == bn_v a * eval_ bLen b i)

let rec bn_mul_loop_lemma #t #aLen #bLen a b i =
  let res = create (aLen + bLen) (uint #t 0) in
  let resi = repeati i (bn_mul_ a b) res in
  if i = 0 then begin
    eq_repeati0 i (bn_mul_ a b) res;
    bn_eval0 b;
    bn_eval_zeroes #t (aLen + bLen) (aLen + i);
    () end
  else begin
    unfold_repeati i (bn_mul_ a b) res (i - 1);
    let resi1 = repeati (i - 1) (bn_mul_ a b) res in
    assert (resi == bn_mul_ a b (i - 1) resi1);
    bn_mul_loop_lemma a b (i - 1);
    assert (eval_ (aLen + bLen) resi1 (aLen + i - 1) == bn_v a * eval_ bLen b (i - 1));
    bn_mul_loop_lemma_step a b i resi1;
    assert (eval_ (aLen + bLen) resi (aLen + i) == bn_v a * eval_ bLen b i);
    () end


val bn_mul_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t bLen ->
  Lemma (bn_v (bn_mul a b) == bn_v a * bn_v b)

let bn_mul_lemma #t #aLen #bLen a b =
  bn_mul_loop_lemma a b bLen


///////////////////

val bn_mul0_lemma_eval:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_pos{aLen + bLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t bLen ->
  Lemma (let res0 = create (aLen + bLen) (uint #t 0) in
    let res = bn_mul_ a b 0 res0 in
    bn_v res == bn_v a * v b.[0])

let bn_mul0_lemma_eval #t #aLen #bLen a b =
  let resLen = aLen + bLen in
  let res0 = create (aLen + bLen) (uint #t 0) in
  let res_mul1 = bn_mul_ a b 0 res0 in

  bn_mul_lemma_ a b 0 res0;
  assert_norm (pow2 0 = 1);
  bn_eval_zeroes #t resLen aLen;
  assert (v res_mul1.[aLen] * pow2 (bits t * aLen) + eval_ resLen res_mul1 aLen == bn_v a * v b.[0]);
  assert (slice res0 (aLen + 1) resLen == slice res_mul1 (aLen + 1) resLen);

  eq_intro (slice res_mul1 (aLen + 1) resLen) (create (resLen - aLen - 1) (uint #t 0));
  bn_eval_zeroes #t (resLen - aLen - 1) (resLen - aLen - 1);
  bn_eval_split_i res_mul1 (aLen + 1);
  assert (bn_v res_mul1 == bn_v (sub res_mul1 0 (aLen + 1)));
  bn_eval_split_i (sub res_mul1 0 (aLen + 1)) aLen;
  bn_eval1 (sub res_mul1 aLen 1);
  assert (bn_v res_mul1 == bn_v (sub res_mul1 0 aLen) + pow2 (bits t * aLen) * v res_mul1.[aLen]);
  bn_eval_extensionality_j (sub res_mul1 0 aLen) res_mul1 aLen;
  assert (bn_v res_mul1 = bn_v a * v b.[0])


val bn_mul_unroll1_is_bn_mul:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_pos{aLen + bLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t bLen ->
  Lemma (bn_mul_unroll1 a b == bn_mul a b)

let bn_mul_unroll1_is_bn_mul #t #aLen #bLen a b =
  let resLen = aLen + bLen in
  let res0 : lbignum t resLen = create resLen (uint #t 0) in

  let res_mul = repeati bLen (bn_mul_ a b) res0 in
  repeati_def bLen (bn_mul_ a b) res0;
  assert (res_mul == repeat_right 0 bLen (fixed_a (lbignum t resLen)) (bn_mul_ a b) res0);

  repeat_right_plus 0 1 bLen (fixed_a (lbignum t resLen)) (bn_mul_ a b) res0;
  let res_mul1 : lbignum t resLen = repeat_right 0 1 (fixed_a (lbignum t resLen)) (bn_mul_ a b) res0 in
  assert (res_mul == repeat_right 1 bLen (fixed_a (lbignum t resLen)) (bn_mul_ a b) res_mul1);

  unfold_repeat_right 0 1 (fixed_a (lbignum t resLen)) (bn_mul_ a b) res0 0;
  eq_repeat_right 0 1 (fixed_a (lbignum t resLen)) (bn_mul_ a b) res0;
  assert (res_mul1 == bn_mul_ a b 0 res0);

  bn_mul0_lemma_eval #t #aLen #bLen a b;
  assert (bn_v res_mul1 = bn_v a * v b.[0]);

  let c, ab0 = bn_mul1 a b.[0] in
  bn_mul1_lemma a b.[0];
  assert (v c * pow2 (bits t * aLen) + bn_v ab0 = bn_v a * v b.[0]);

  let res1 = update_sub res0 0 aLen ab0 in
  bn_eval_update_sub aLen ab0 resLen;
  assert (bn_v res1 = bn_v ab0);

  let res2 = res1.[aLen] <- c in
  bn_upd_eval res1 c aLen;
  assert (v res1.[aLen] = 0);
  assert (bn_v res2 = bn_v a * v b.[0]);

  bn_eval_inj resLen res2 res_mul1;
  assert (res_mul1 == res2)
