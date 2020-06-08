module Hacl.Spec.Bignum.Multiplication

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum.Base
open Hacl.Spec.Lib


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val lemma_mul_carry_add_64: a:uint64 -> b:uint64 -> c:uint64 -> d:uint64 ->
  Lemma (uint_v a * uint_v b + uint_v c + uint_v d < pow2 128)
let lemma_mul_carry_add_64 a b c d =
  let n = pow2 64 in
  //assert (uint_v a <= n - 1 /\ uint_v b <= n - 1 /\ uint_v c <= n - 1 /\ uint_v d <= n - 1);
  Math.Lemmas.lemma_mult_le_left (uint_v a) (uint_v b) (n - 1);
  Math.Lemmas.lemma_mult_le_right (n - 1) (uint_v a) (n - 1);
  assert (uint_v a * uint_v b + uint_v c + uint_v d <= (n - 1) * (n - 1) + (n - 1) + (n - 1));
  assert ((n - 1) * (n - 1) + (n - 1) + (n - 1) == n * n - 1);
  FStar.Math.Lemmas.pow2_plus 64 64


inline_for_extraction noextract
val mul_carry_add_u64: a:uint64 -> b:uint64 -> c:uint64 -> d:uint64 ->
  Pure (tuple2 uint64 uint64)
  (requires True)
  (ensures  fun (c', r) ->
    uint_v r + uint_v c' * pow2 64 == uint_v a * uint_v b + uint_v c + uint_v d)

let mul_carry_add_u64 a b c d =
  lemma_mul_carry_add_64 a b c d;
  let res = mul64_wide a b +! to_u128 #U64 c +! to_u128 #U64 d in
  let r = to_u64 res in
  let c' = to_u64 (res >>. 64ul) in
  c', r

val bn_mul1_add_in_place_f:
    #aLen:size_nat
  -> a:lbignum aLen
  -> l:uint64
  -> acc:lbignum aLen
  -> i:size_nat{i < aLen}
  -> c:uint64 ->
  uint64 & uint64 // carry & out

let bn_mul1_add_in_place_f #aLen a l acc i c =
  mul_carry_add_u64 a.[i] l c acc.[i]


val bn_mul1_add_in_place:
    #aLen:size_nat
  -> a:lbignum aLen
  -> l:uint64
  -> acc:lbignum aLen ->
  uint64 & lbignum aLen

let bn_mul1_add_in_place #aLen a l acc =
  generate_elems aLen aLen (bn_mul1_add_in_place_f a l acc) (u64 0)


val bn_mul1_lshift_add:
    #aLen:size_nat
  -> #resLen:size_nat
  -> a:lbignum aLen
  -> b_j:uint64
  -> j:size_nat{j + aLen <= resLen}
  -> res:lbignum resLen ->
  uint64 & lbignum resLen

let bn_mul1_lshift_add #aLen #resLen a b_j j res =
  let res' = sub res j aLen in
  let c, res' = bn_mul1_add_in_place #aLen a b_j res' in
  let res = update_sub res j aLen res' in
  c, res


val bn_mul_:
    #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> j:size_nat{j < bLen}
  -> res:lbignum (aLen + bLen) ->
  lbignum (aLen + bLen)

let bn_mul_ #aLen #bLen a b j res =
  let c, res = bn_mul1_lshift_add #aLen #(aLen+bLen) a b.[j] j res in
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


val bn_mul1_add_in_place_lemma_loop_step:
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
    let (c, res) = generate_elem_f #uint64 #uint64 aLen (bn_mul1_add_in_place_f a l acc) (i - 1) (c1, res1) in
    v c * pow2 (64 * i) + bn_v #i res == eval_ aLen acc i + eval_ aLen a i * v l))

let bn_mul1_add_in_place_lemma_loop_step #aLen a l acc i (c1, res1) =
  let (c, res) = generate_elem_f #uint64 #uint64 aLen (bn_mul1_add_in_place_f a l acc) (i - 1) (c1, res1) in
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


val bn_mul1_add_in_place_lemma_loop:
    #aLen:size_nat
  -> a:lbignum aLen
  -> l:uint64
  -> acc:lbignum aLen
  -> i:nat{i <= aLen} -> Lemma
  (let (c, res) : generate_elem_a uint64 uint64 aLen i = generate_elems aLen i (bn_mul1_add_in_place_f a l acc) (u64 0) in
   v c * pow2 (64 * i) + bn_v #i res == eval_ aLen acc i + eval_ aLen a i * v l)

let rec bn_mul1_add_in_place_lemma_loop #aLen a l acc i =
  let (c, res) : generate_elem_a uint64 uint64 aLen i = generate_elems aLen i (bn_mul1_add_in_place_f a l acc) (u64 0) in
  if i = 0 then begin
    eq_generate_elems0 #uint64 #uint64 aLen i (bn_mul1_add_in_place_f a l acc) (u64 0);
    assert (c == u64 0 /\ res == Seq.empty);
    bn_eval0 #0 res;
    assert_norm (pow2 0 = 1);
    bn_eval0 a;
    bn_eval0 acc;
    () end
  else begin
    let (c1, res1) : generate_elem_a uint64 uint64 aLen (i - 1) = generate_elems aLen (i - 1) (bn_mul1_add_in_place_f a l acc) (u64 0) in
    generate_elems_unfold #uint64 #uint64 aLen i (bn_mul1_add_in_place_f a l acc) (u64 0) (i - 1);
    assert (generate_elems #uint64 #uint64 aLen i (bn_mul1_add_in_place_f a l acc) (u64 0) ==
      generate_elem_f aLen (bn_mul1_add_in_place_f a l acc) (i - 1) (generate_elems #uint64 #uint64 aLen (i - 1) (bn_mul1_add_in_place_f a l acc) (u64 0)));
    assert ((c, res) == generate_elem_f #uint64 #uint64 aLen (bn_mul1_add_in_place_f a l acc) (i - 1) (c1, res1));
    bn_mul1_add_in_place_lemma_loop #aLen a l acc (i - 1);
    assert (v c1 * pow2 (64 * (i - 1)) + bn_v #(i - 1) res1 == eval_ aLen acc (i - 1) + eval_ aLen a (i - 1) * v l);
    bn_mul1_add_in_place_lemma_loop_step #aLen a l acc i (c1, res1);
    assert (v c * pow2 (64 * i) + bn_v #i res == eval_ aLen acc i + eval_ aLen a i * v l);
    () end


val bn_mul1_add_in_place_lemma:
    #aLen:size_nat
  -> a:lbignum aLen
  -> l:uint64
  -> acc:lbignum aLen -> Lemma
  (let (c, res) = bn_mul1_add_in_place #aLen a l acc in
   v c * pow2 (64 * aLen) + bn_v res == bn_v acc + bn_v a * v l)

let bn_mul1_add_in_place_lemma #aLen a l acc =
  let (c, res) = bn_mul1_add_in_place #aLen a l acc in
  bn_mul1_add_in_place_lemma_loop #aLen a l acc aLen


val bn_mul1_lshift_add_lemma:
    #aLen:size_nat
  -> #resLen:size_nat
  -> a:lbignum aLen
  -> b_j:uint64
  -> j:size_nat{j + aLen <= resLen}
  -> acc:lbignum resLen -> Lemma
  (let (c, res) = bn_mul1_lshift_add #aLen #resLen a b_j j acc in
   v c * pow2 (64 * (aLen + j)) + eval_ resLen res (aLen + j) ==
   eval_ resLen acc (aLen + j) + bn_v a * v b_j * pow2 (64 * j))

let bn_mul1_lshift_add_lemma #aLen #resLen a b_j j acc =
  let res1 = sub acc j aLen in
  let c, res2 = bn_mul1_add_in_place #aLen a b_j res1 in
  bn_mul1_add_in_place_lemma #aLen a b_j res1;
  assert (v c * pow2 (64 * aLen) + bn_v res2 == bn_v res1 + bn_v a * v b_j);
  let res = update_sub acc j aLen res2 in
  bn_eval_split_i (sub res 0 (j + aLen)) j;
  bn_eval_extensionality_j res (sub res 0 (j + aLen)) (j + aLen);
  assert (eval_ resLen res (j + aLen) == bn_v #j (sub res 0 j) + pow2 (64 * j) * bn_v res2);
  eq_intro (sub res 0 j) (sub acc 0 j);
  assert (bn_v #j (sub res 0 j) == bn_v #j (sub acc 0 j));
  bn_eval_split_i (sub acc 0 (j + aLen)) j;
  bn_eval_extensionality_j acc (sub acc 0 (j + aLen)) (j + aLen);
  assert (eval_ resLen acc (j + aLen) == bn_v #j (sub acc 0 j) + pow2 (64 * j) * bn_v res1);

  calc (==) {
    v c * pow2 (64 * (aLen + j)) + eval_ resLen res (aLen + j);
    (==) { Math.Lemmas.pow2_plus (64 * aLen) (64 * j) }
    v c * (pow2 (64 * aLen) * pow2 (64 * j)) + eval_ resLen res (aLen + j);
    (==) { Math.Lemmas.paren_mul_right (v c) (pow2 (64 * aLen)) (pow2 (64 * j)) }
    v c * pow2 (64 * aLen) * pow2 (64 * j) + eval_ resLen res (aLen + j);
    (==) { }
    (bn_v res1 + bn_v a * v b_j - bn_v res2) * pow2 (64 * j) + eval_ resLen res (aLen + j);
    (==) { }
    (bn_v res1 + bn_v a * v b_j - bn_v res2) * pow2 (64 * j) + eval_ resLen acc (j + aLen) - pow2 (64 * j) * bn_v res1 + pow2 (64 * j) * bn_v res2;
    (==) { Math.Lemmas.distributivity_add_right (pow2 (64 * j)) (bn_v res1) (bn_v a * v b_j - bn_v res2) }
    pow2 (64 * j) * (bn_v a * v b_j - bn_v res2) + eval_ resLen acc (j + aLen) + pow2 (64 * j) * bn_v res2;
    (==) { Math.Lemmas.distributivity_sub_right (pow2 (64 * j)) (bn_v a * v b_j) (bn_v res2) }
    pow2 (64 * j) * (bn_v a * v b_j) + eval_ resLen acc (j + aLen);
  };
  assert (v c * pow2 (64 * (aLen + j)) + eval_ resLen res (aLen + j) ==
    eval_ resLen acc (aLen + j) + bn_v a * v b_j * pow2 (64 * j))


val bn_mul_lemma_:
    #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> j:size_nat{j < bLen}
  -> acc:lbignum (aLen + bLen) -> Lemma
  (let res = bn_mul_ a b j acc in
   v res.[aLen + j] * pow2 (64 * (aLen + j)) + eval_ (aLen + bLen) res (aLen + j) ==
   eval_ (aLen + bLen) acc (aLen + j) + bn_v a * v b.[j] * pow2 (64 * j))

let bn_mul_lemma_ #aLen #bLen a b j acc =
  let c, res = bn_mul1_lshift_add #aLen #(aLen+bLen) a b.[j] j acc in
  bn_mul1_lshift_add_lemma #aLen #(aLen+bLen) a b.[j] j acc;

  let res1 = res.[aLen + j] <- c in
  bn_eval_extensionality_j res res1 (aLen + j)


val bn_mul_loop_lemma_step:
    #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> i:pos{i <= bLen}
  -> resi1:lbignum (aLen + bLen) -> Lemma
  (requires eval_ (aLen + bLen) resi1 (aLen + i - 1) == bn_v a * eval_ bLen b (i - 1))
  (ensures
    (let resi = bn_mul_ #aLen #bLen a b (i - 1) resi1 in
    eval_ (aLen + bLen) resi (aLen + i) == bn_v a * eval_ bLen b i))

let bn_mul_loop_lemma_step #aLen #bLen a b i resi1 =
  let resi = bn_mul_ #aLen #bLen a b (i - 1) resi1 in
  bn_mul_lemma_ #aLen #bLen a b (i - 1) resi1;
  assert
    (v resi.[aLen + i - 1] * pow2 (64 * (aLen + i - 1)) + eval_ (aLen + bLen) resi (aLen + i - 1) ==
     eval_ (aLen + bLen) resi1 (aLen + i - 1) + bn_v a * v b.[i - 1] * pow2 (64 * (i - 1)));

  calc (==) {
    eval_ (aLen + bLen) resi (aLen + i);
    (==) { bn_eval_unfold_i resi (aLen + i) }
    eval_ (aLen + bLen) resi (aLen + i - 1) + v resi.[aLen + i - 1] * pow2 (64 * (aLen + i - 1));
    (==) { }
    eval_ (aLen + bLen) resi1 (aLen + i - 1) + bn_v a * v b.[i - 1] * pow2 (64 * (i - 1));
    (==) { }
    bn_v a * eval_ bLen b (i - 1) + bn_v a * v b.[i - 1] * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.paren_mul_right (bn_v a) (v b.[i - 1]) (pow2 (64 * (i - 1))) }
    bn_v a * eval_ bLen b (i - 1) + bn_v a * (v b.[i - 1] * pow2 (64 * (i - 1)));
    (==) { Math.Lemmas.distributivity_add_right (bn_v a) (eval_ bLen b (i - 1)) (v b.[i - 1] * pow2 (64 * (i - 1))) }
    bn_v a * (eval_ bLen b (i - 1) + v b.[i - 1] * pow2 (64 * (i - 1)));
    (==) { bn_eval_unfold_i b i }
    bn_v a * eval_ bLen b i;
  };
  assert (eval_ (aLen + bLen) resi (aLen + i) == bn_v a * eval_ bLen b i)


val bn_mul_loop_lemma:
    #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> i:nat{i <= bLen} -> Lemma
  (let res = create (aLen + bLen) (u64 0) in
   let resi = repeati i (bn_mul_ #aLen #bLen a b) res in
   eval_ (aLen + bLen) resi (aLen + i) == bn_v a * eval_ bLen b i)

let rec bn_mul_loop_lemma #aLen #bLen a b i =
  let res = create (aLen + bLen) (u64 0) in
  let resi = repeati i (bn_mul_ #aLen #bLen a b) res in
  if i = 0 then begin
    eq_repeati0 i (bn_mul_ #aLen #bLen a b) res;
    bn_eval0 b;
    bn_eval_zeroes (aLen + bLen) (aLen + i);
    () end
  else begin
    unfold_repeati i (bn_mul_ #aLen #bLen a b) res (i - 1);
    let resi1 = repeati (i - 1) (bn_mul_ #aLen #bLen a b) res in
    assert (resi == bn_mul_ #aLen #bLen a b (i - 1) resi1);
    bn_mul_loop_lemma #aLen #bLen a b (i - 1);
    assert (eval_ (aLen + bLen) resi1 (aLen + i - 1) == bn_v a * eval_ bLen b (i - 1));
    bn_mul_loop_lemma_step #aLen #bLen a b i resi1;
    assert (eval_ (aLen + bLen) resi (aLen + i) == bn_v a * eval_ bLen b i);
    () end


val bn_mul_lemma:
    #aLen:size_nat
  -> #bLen:size_nat{aLen + bLen <= max_size_t}
  -> a:lbignum aLen
  -> b:lbignum bLen -> Lemma
  (bn_v (bn_mul #aLen #bLen a b) == bn_v a * bn_v b)

let bn_mul_lemma #aLen #bLen a b =
  bn_mul_loop_lemma #aLen #bLen a b bLen
