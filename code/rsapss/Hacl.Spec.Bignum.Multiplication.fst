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


val bn_sqr_diag_f:
    #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum aLen
  -> i:nat{i < aLen}
  -> acc:lbignum (aLen + aLen) ->
  lbignum (aLen + aLen)

let bn_sqr_diag_f #aLen a i acc =
  let a2 = mul64_wide a.[i] a.[i] in
  let acc = acc.[2 * i] <- to_u64 a2 in
  let acc = acc.[2 * i + 1] <- to_u64 (a2 >>. 64ul) in
  acc


val bn_sqr_diag:
    #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum aLen ->
  lbignum (aLen + aLen)

let bn_sqr_diag #aLen a =
  let acc0 = create (aLen + aLen) (u64 0) in
  repeati aLen (bn_sqr_diag_f #aLen a) acc0


val bn_sqr_f:
    #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum aLen
  -> j:nat{j < aLen}
  -> acc:lbignum (aLen + aLen) ->
  lbignum (aLen + aLen)

let bn_sqr_f #aLen a j acc =
  let c, acc = bn_mul1_lshift_add (sub a 0 j) a.[j] j acc in
  acc.[j + j] <- c


val bn_sqr: #aLen:size_nat{aLen + aLen <= max_size_t} -> a:lbignum aLen -> lbignum (aLen + aLen)
let bn_sqr #aLen a =
  let res = create (aLen + aLen) (u64 0) in
  let res = repeati aLen (bn_sqr_f a) res in
  let c, res = Hacl.Spec.Bignum.Addition.bn_add res res in
  let tmp = bn_sqr_diag a in
  let c, res = Hacl.Spec.Bignum.Addition.bn_add res tmp in
  res


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
   eval_ resLen acc (aLen + j) + bn_v a * v b_j * pow2 (64 * j) /\
   slice res (aLen + j) resLen == slice acc (aLen + j) resLen)

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
    eval_ resLen acc (aLen + j) + bn_v a * v b_j * pow2 (64 * j));
  eq_intro (slice res (aLen + j) resLen) (slice acc (aLen + j) resLen)


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


val bn_sqr_diag_inductive: #aLen:size_nat{aLen + aLen <= max_size_t} -> a:lbignum aLen -> k:nat{k <= aLen} ->
  Pure (lbignum (aLen + aLen))
  (requires True)
  (ensures fun res ->
    (let acc0 = create (aLen + aLen) (u64 0) in
    res == repeati k (bn_sqr_diag_f #aLen a) acc0 /\
    (forall (i:nat{i < k}).
      Seq.index res (2 * i) == to_u64 (mul64_wide a.[i] a.[i]) /\
      Seq.index res (2 * i + 1) == to_u64 (mul64_wide a.[i] a.[i] >>. 64ul)) /\
    (forall (i:nat{k <= i /\ i < aLen}).
      Seq.index res (2 * i) == Seq.index acc0 (2 * i) /\
      Seq.index res (2 * i + 1) == Seq.index acc0 (2 * i + 1))))

let bn_sqr_diag_inductive #aLen a k =
  let acc0 = create (aLen + aLen) (u64 0) in
  eq_repeati0 k (bn_sqr_diag_f #aLen a) acc0;
  repeati_inductive k
  (fun i acci ->
    acci == repeati i (bn_sqr_diag_f #aLen a) acc0 /\
    (forall (i0:nat{i0 < i}).
      Seq.index acci (2 * i0) == to_u64 (mul64_wide a.[i0] a.[i0]) /\
      Seq.index acci (2 * i0 + 1) == to_u64 (mul64_wide a.[i0] a.[i0] >>. 64ul)) /\
    (forall (i0:nat{i <= i0 /\ i0 < aLen}).
      Seq.index acci (2 * i0) == Seq.index acc0 (2 * i0) /\
      Seq.index acci (2 * i0 + 1) == Seq.index acc0 (2 * i0 + 1)))
  (fun i acci ->
    let acc = bn_sqr_diag_f #aLen a i acci in
    unfold_repeati (i + 1) (bn_sqr_diag_f #aLen a) acc0 i;
    acc)
  acc0


val bn_sqr_diag_lemma: #aLen:size_nat{aLen + aLen <= max_size_t} -> a:lbignum aLen -> k:nat{k <= aLen} -> Lemma
  (let acc0 = create (aLen + aLen) (u64 0) in
   let acc : lbignum (aLen + aLen) = repeati k (bn_sqr_diag_f #aLen a) acc0 in
  (forall (i:nat{i < k}).
    Seq.index acc (2 * i) == to_u64 (mul64_wide a.[i] a.[i]) /\
    Seq.index acc (2 * i + 1) == to_u64 (mul64_wide a.[i] a.[i] >>. 64ul)) /\
  (forall (i:nat{k <= i /\ i < aLen}).
    Seq.index acc (2 * i) == Seq.index acc0 (2 * i) /\
    Seq.index acc (2 * i + 1) == Seq.index acc0 (2 * i + 1)))

let bn_sqr_diag_lemma #aLen a k =
  let _ = bn_sqr_diag_inductive #aLen a k in ()


val bn_sqr_diag_eq: #aLen:size_nat{aLen + aLen <= max_size_t} -> a:lbignum aLen -> k:nat{k < aLen} -> Lemma
  (let acc0 = create (aLen + aLen) (u64 0) in
   let acc1 : lbignum (aLen + aLen) = repeati k (bn_sqr_diag_f #aLen a) acc0 in
   let acc2 : lbignum (aLen + aLen) = repeati (k + 1) (bn_sqr_diag_f #aLen a) acc0 in
   slice acc1 0 (2 * k) == slice acc2 0 (2 * k))

let bn_sqr_diag_eq #aLen a k =
  let acc0 = create (aLen + aLen) (u64 0) in
  let acc1 : lbignum (aLen + aLen) = repeati k (bn_sqr_diag_f #aLen a) acc0 in
  let acc2 : lbignum (aLen + aLen) = repeati (k + 1) (bn_sqr_diag_f #aLen a) acc0 in

  let aux (i:nat{i < 2 * k}) : Lemma (Seq.index acc1 i == Seq.index acc2 i) =
    let i2 = i / 2 in
    bn_sqr_diag_lemma #aLen a k;
    bn_sqr_diag_lemma #aLen a (k + 1);
    assert
     (Seq.index acc1 (2 * i2) == Seq.index acc2 (2 * i2) /\
      Seq.index acc1 (2 * i2 + 1) == Seq.index acc2 (2 * i2 + 1));
    Math.Lemmas.euclidean_division_definition i 2;
    assert (Seq.index acc1 i == Seq.index acc2 i) in

  Classical.forall_intro aux;
  eq_intro (slice acc1 0 (2 * k)) (slice acc2 0 (2 * k))


val bn_sqr_diag_loop_step:
    #aLen:size_pos{aLen + aLen <= max_size_t}
  -> a:lbignum aLen
  -> i:pos{i <= aLen} -> Lemma
  (let acc0 = create (aLen + aLen) (u64 0) in
   let acc1 : lbignum (aLen + aLen) = repeati i (bn_sqr_diag_f #aLen a) acc0 in
   let acc2 : lbignum (aLen + aLen) = repeati (i - 1) (bn_sqr_diag_f #aLen a) acc0 in
   eval_ (aLen + aLen) acc1 (i + i) == eval_ (aLen + aLen) acc2 (i + i - 2) + v a.[i - 1] * v a.[i - 1] * pow2 (64 * (i + i - 2)))

let bn_sqr_diag_loop_step #aLen a i =
  let acc0 = create (aLen + aLen) (u64 0) in
  let acc1 : lbignum (aLen + aLen) = repeati i (bn_sqr_diag_f #aLen a) acc0 in
  let acc2 : lbignum (aLen + aLen) = repeati (i - 1) (bn_sqr_diag_f #aLen a) acc0 in

  bn_eval_unfold_i acc1 (i + i);
  bn_eval_unfold_i acc1 (i + i - 1);
  //assert (eval_ (aLen + aLen) acc1 (i + i) ==
    //eval_ (aLen + aLen) acc1 (i + i - 2) + v acc1.[i + i - 2] * pow2 (64 * (i + i - 2)) + v acc1.[i + i - 1] * pow2 (64 * (i + i - 1)));

  calc (==) {
    v acc1.[i + i - 2] * pow2 (64 * (i + i - 2)) + v acc1.[i + i - 1] * pow2 (64 * (i + i - 1));
    (==) { Math.Lemmas.pow2_plus (64 * (i + i - 2)) 64 }
    v acc1.[i + i - 2] * pow2 (64 * (i + i - 2)) + v acc1.[i + i - 1] * (pow2 (64 * (i + i - 2)) * pow2 64);
    (==) { Math.Lemmas.paren_mul_right (v acc1.[i + i - 1]) (pow2 64) (pow2 (64 * (i + i - 2))) }
    v acc1.[i + i - 2] * pow2 (64 * (i + i - 2)) + (v acc1.[i + i - 1] * pow2 64) * pow2 (64 * (i + i - 2));
    (==) { Math.Lemmas.distributivity_add_left (v acc1.[i + i - 2]) (v acc1.[i + i - 1] * pow2 64) (pow2 (64 * (i + i - 2))) }
    (v acc1.[i + i - 2] + v acc1.[i + i - 1] * pow2 64) * pow2 (64 * (i + i - 2));
    (==) { bn_sqr_diag_lemma #aLen a i }
    v a.[i - 1] * v a.[i - 1] * pow2 (64 * (i + i - 2));
  };

  bn_sqr_diag_eq #aLen a (i - 1);
  bn_eval_extensionality_j acc1 acc2 (i + i - 2);

  assert (eval_ (aLen + aLen) acc1 (i + i) ==
    eval_ (aLen + aLen) acc2 (i + i - 2) + v a.[i - 1] * v a.[i - 1] * pow2 (64 * (i + i - 2)))


val bn_sqr_f_lemma:
    #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum aLen
  -> j:size_nat{j < aLen}
  -> acc:lbignum (aLen + aLen) -> Lemma
  (let res = bn_sqr_f a j acc in
   eval_ (aLen + aLen) res (j + j + 1) == eval_ (aLen + aLen) acc (j + j) + eval_ aLen a j * v a.[j] * pow2 (64 * j) /\
  (forall (i:nat{j + j < i /\ i < aLen + aLen}). index res i == index acc i))

let bn_sqr_f_lemma #aLen a j acc =
  let resLen = aLen + aLen in

  let c, acc' = bn_mul1_add_in_place #j (sub a 0 j) a.[j] (sub acc j j) in
  let acc1 = update_sub acc j j acc' in
  assert (forall (i:nat{j + j <= i /\ i < aLen + aLen}). index acc1 i == index acc i);
  let res = acc1.[j + j] <- c in
  assert (forall (i:nat{j + j < i /\ i < aLen + aLen}). index res i == index acc i);

  bn_mul1_lshift_add_lemma #j #resLen (sub a 0 j) a.[j] j acc;
  //assert (v c * pow2 (64 * (j + j)) + eval_ resLen acc1 (j + j) == eval_ resLen acc (j + j) + bn_v (sub a 0 j) * v a.[j] * pow2 (64 * j));
  bn_eval_extensionality_j acc1 res (j + j);
  //assert (v res.[j + j] * pow2 (64 * (j + j)) + eval_ resLen res (j + j) == eval_ resLen acc (j + j) + bn_v (sub a 0 j) * v a.[j] * pow2 (64 * j));
  bn_eval_unfold_i res (j + j + 1);
  //assert (eval_ resLen res (j + j + 1) == eval_ resLen acc (j + j) + bn_v (sub a 0 j) * v a.[j] * pow2 (64 * j));
  bn_eval_extensionality_j a (sub a 0 j) j
  //assert (eval_ resLen res (j + j + 1) == eval_ resLen acc (j + j) + eval_ aLen a j * v a.[j] * pow2 (64 * j))


val bn_sqr_inductive: #aLen:size_nat{aLen + aLen <= max_size_t} -> a:lbignum aLen -> k:nat{k <= aLen} ->
  Pure (lbignum (aLen + aLen))
  (requires True)
  (ensures fun res ->
    (let acc0 = create (aLen + aLen) (u64 0) in
    res == repeati k (bn_sqr_f #aLen a) acc0 /\
    (forall (i:nat{k + k < i /\ i < aLen + aLen}). Seq.index res i == Seq.index acc0 i)))

let bn_sqr_inductive #aLen a k =
  let acc0 = create (aLen + aLen) (u64 0) in
  eq_repeati0 k (bn_sqr_f #aLen a) acc0;
  repeati_inductive #(lbignum (aLen + aLen)) k
  (fun i acci ->
    acci == repeati i (bn_sqr_f #aLen a) acc0 /\
    (forall (i0:nat{i + i < i0 /\ i0 < aLen + aLen}). Seq.index acci i0 == Seq.index acc0 i0))
  (fun i acci ->
    let c, res' = bn_mul1_add_in_place #i (sub a 0 i) a.[i] (sub acci i i) in
    let acc = update_sub acci i i res' in
    let acc1 = acc.[i + i] <- c in
    //assert (forall (i0:nat{i + i < i0 /\ i0 < aLen + aLen}). index acc i0 == index acci i0);
    assert (forall (i0:nat{i + i < i0 /\ i0 < aLen + aLen}). index acc1 i0 == index acc i0);
    //assert (forall (i0:nat{i + i < i0 /\ i0 < aLen + aLen}). index acc1 i0 == index acci i0);
    unfold_repeati (i + 1) (bn_sqr_f #aLen a) acc0 i;
    acc1)
  acc0


val bn_sqr_tail: #aLen:size_nat{aLen + aLen <= max_size_t} -> a:lbignum aLen -> k:nat{k <= aLen} -> Lemma
  (let acc0 = create (aLen + aLen) (u64 0) in
   let acc : lbignum (aLen + aLen) = repeati k (bn_sqr_f #aLen a) acc0 in
   (forall (i:nat{k + k < i /\ i < aLen + aLen}). Seq.index acc i == u64 0))

let bn_sqr_tail #aLen a k =
  let _ = bn_sqr_inductive a k in ()


val square_of_sum: a:nat -> b:nat -> Lemma ((a + b) * (a + b) == a * a + 2 * a * b + b * b)
let square_of_sum a b = ()


val bn_eval_square: #aLen:size_nat{aLen + aLen <= max_size_t} -> a:lbignum aLen -> i:pos{i <= aLen} ->
  Lemma (eval_ aLen a i * eval_ aLen a i == eval_ aLen a (i - 1) * eval_ aLen a (i - 1) +
    2 * eval_ aLen a (i - 1) * v a.[i - 1] * pow2 (64 * (i - 1)) + v a.[i - 1] * v a.[i - 1] * pow2 (64 * (i + i - 2)))

let bn_eval_square #aLen a i =
  let e1 = eval_ aLen a (i - 1) in
  let p1 = pow2 (64 * (i - 1)) in
  let p2 = pow2 (64 * (i + i - 2)) in

  calc (==) {
    eval_ aLen a i * eval_ aLen a i;
    (==) { bn_eval_unfold_i a i }
    (e1 + v a.[i - 1] * p1) * (e1 + v a.[i - 1] * p1);
    (==) { square_of_sum e1 (v a.[i - 1] * p1) }
    e1 * e1 + 2 * e1 * (v a.[i - 1] * p1) + (v a.[i - 1] * p1) * (v a.[i - 1] * p1);
    (==) { Math.Lemmas.paren_mul_right (v a.[i - 1]) p1 (v a.[i - 1] * p1); Math.Lemmas.paren_mul_right p1 p1 (v a.[i - 1]) }
    e1 * e1 + 2 * e1 * (v a.[i - 1] * p1) + v a.[i - 1] * (p1 * p1 * v a.[i - 1]);
    (==) { Math.Lemmas.pow2_plus (64 * (i - 1)) (64 * (i - 1)) }
    e1 * e1 + 2 * e1 * (v a.[i - 1] * p1) + v a.[i - 1] * (p2 * v a.[i - 1]);
    (==) { Math.Lemmas.paren_mul_right (v a.[i - 1]) (v a.[i - 1]) p2 }
    e1 * e1 + 2 * e1 * (v a.[i - 1] * p1) + v a.[i - 1] * v a.[i - 1] * p2;
    (==) { Math.Lemmas.paren_mul_right (2 * e1) (v a.[i - 1]) p1 }
    e1 * e1 + 2 * e1 * v a.[i - 1] * p1 + v a.[i - 1] * v a.[i - 1] * p2;
    }


val bn_sqr_loop_lemma:
    #aLen:size_nat{aLen + aLen <= max_size_t}
  -> a:lbignum aLen
  -> i:nat{i <= aLen} -> Lemma
  (let resLen = aLen + aLen in
   let bn_zero = create (aLen + aLen) (u64 0) in
   let acc : lbignum (aLen + aLen) = repeati i (bn_sqr_f a) bn_zero in
   let tmp : lbignum (aLen + aLen) = repeati i (bn_sqr_diag_f a) bn_zero in
   2 * eval_ resLen acc (i + i) + eval_ resLen tmp (i + i) == eval_ aLen a i * eval_ aLen a i)

let rec bn_sqr_loop_lemma #aLen a i =
  let resLen = aLen + aLen in
  let bn_zero = create (aLen + aLen) (u64 0) in
  let acc : lbignum (aLen + aLen) = repeati i (bn_sqr_f a) bn_zero in
  let tmp : lbignum (aLen + aLen) = repeati i (bn_sqr_diag_f a) bn_zero in

  if i = 0 then begin
    bn_eval0 acc;
    bn_eval0 tmp;
    bn_eval0 a end
  else begin
    let acc1 : lbignum (aLen + aLen) = repeati (i - 1) (bn_sqr_f a) bn_zero in
    let tmp1 : lbignum (aLen + aLen) = repeati (i - 1) (bn_sqr_diag_f a) bn_zero in

    unfold_repeati i (bn_sqr_f a) bn_zero (i - 1);
    assert (acc == bn_sqr_f a (i - 1) acc1);

    calc (==) {
      eval_ resLen acc (i + i);
      (==) { bn_eval_unfold_i acc (i + i) }
      eval_ resLen acc (i + i - 1) + v acc.[i + i - 1] * pow2 (64 * (i + i - 1));
      (==) { bn_sqr_f_lemma a (i - 1) acc1 }
      eval_ resLen acc1 (i + i - 2) + eval_ aLen a (i - 1) * v a.[i - 1] * pow2 (64 * (i - 1)) + v acc.[i + i - 1] * pow2 (64 * (i + i - 1));
      };

    bn_sqr_f_lemma a (i - 1) acc1;
    assert (acc.[i + i - 1] == acc1.[i + i - 1]);
    bn_sqr_tail #aLen a (i - 1);
    assert (acc.[i + i - 1] == u64 0);

    calc (==) {
      2 * eval_ resLen acc (i + i) + eval_ resLen tmp (i + i);
      (==) { bn_sqr_diag_loop_step #aLen a i }
      2 * eval_ resLen acc (i + i) + eval_ (aLen + aLen) tmp1 (i + i - 2) + v a.[i - 1] * v a.[i - 1] * pow2 (64 * (i + i - 2));
      (==) { }
      2 * eval_ resLen acc1 (i + i - 2) + 2 * eval_ aLen a (i - 1) * v a.[i - 1] * pow2 (64 * (i - 1)) +
      eval_ (aLen + aLen) tmp1 (i + i - 2) + v a.[i - 1] * v a.[i - 1] * pow2 (64 * (i + i - 2));
      (==) { bn_sqr_loop_lemma #aLen a (i - 1) }
      eval_ aLen a (i - 1) * eval_ aLen a (i - 1) +
      2 * eval_ aLen a (i - 1) * v a.[i - 1] * pow2 (64 * (i - 1)) +
      v a.[i - 1] * v a.[i - 1] * pow2 (64 * (i + i - 2));
      (==) { bn_eval_square #aLen a i }
      eval_ aLen a i * eval_ aLen a i;
    }; () end


val bn_sqr_lemma: #aLen:size_nat{aLen + aLen <= max_size_t} -> a:lbignum aLen -> Lemma
  (bn_v (bn_sqr a) == bn_v a * bn_v a)

let bn_sqr_lemma #aLen a =
  let resLen = aLen + aLen in
  let res0 = create (aLen + aLen) (u64 0) in
  let res1 = repeati aLen (bn_sqr_f a) res0 in
  let c0, res2 = Hacl.Spec.Bignum.Addition.bn_add res1 res1 in
  Hacl.Spec.Bignum.Addition.bn_add_lemma res1 res1;
  let tmp = bn_sqr_diag a in
  let c1, res3 = Hacl.Spec.Bignum.Addition.bn_add res2 tmp in
  Hacl.Spec.Bignum.Addition.bn_add_lemma res2 tmp;
  assert ((v c0 + v c1) * pow2 (64 * resLen) + bn_v res3 == 2 * bn_v res1 + bn_v tmp);
  bn_sqr_loop_lemma #aLen a aLen;
  assert (2 * bn_v res1 + bn_v tmp == bn_v a * bn_v a);
  bn_eval_bound a aLen;
  Math.Lemmas.lemma_mult_lt_sqr (bn_v a) (bn_v a) (pow2 (64 * aLen));
  Math.Lemmas.pow2_plus (64 * aLen) (64 * aLen);
  assert (bn_v a * bn_v a < pow2 (64 * resLen));
  bn_eval_bound res3 resLen;
  assert ((v c0 + v c1) = 0)
