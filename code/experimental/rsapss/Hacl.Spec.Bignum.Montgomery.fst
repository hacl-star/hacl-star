module Hacl.Spec.Bignum.Montgomery

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Addition
open Hacl.Spec.Bignum.Multiplication


module M = Hacl.Spec.Bignum.Montgomery.Lemmas
module BL = Hacl.Spec.Bignum.Lemmas

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val mont_reduction_:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> j:size_nat{j < rLen}
  -> acc:lbignum (rLen + rLen) ->
  lbignum (rLen + rLen)

let mont_reduction_ #nLen #rLen n nInv_u64 j acc =
  let qj = nInv_u64 *. acc.[j] in
  let c, res1 = bn_mul_by_limb_add_shift_j #nLen #(rLen + rLen) n qj j acc in
  let res2 = slice res1 (j + nLen) (rLen + rLen) in
  let _, res3 = bn_add res2 (create 1 c) in
  update_sub res1 (j + nLen) (rLen + rLen - j - nLen) res3


val mont_reduction_f_lemma_bound:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> qj:uint64
  -> c:lbignum (rLen + rLen)
  -> j:size_nat{j < rLen}
  -> acc:lbignum (rLen + rLen) -> Lemma
  (requires
    0 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v c < 4 * bn_v n * bn_v n /\
    bn_v acc <= bn_v c + (pow2 (64 * j) - 1) * bn_v n)
  (ensures
    bn_v acc + bn_v n * v qj * pow2 (64 * j) <= bn_v c + (pow2 (64 * (j + 1)) - 1) * bn_v n /\
    bn_v acc + bn_v n * v qj * pow2 (64 * j) < pow2 (128 * rLen))

let mont_reduction_f_lemma_bound #nLen #rLen n qj c j acc =
  M.mont_reduction_lemma_step_bound_aux rLen (bn_v n) (v qj) (j + 1) (bn_v c) (bn_v acc);
  calc (<) {
    bn_v c + (pow2 (64 * (j + 1)) - 1) * bn_v n;
    (<) { Math.Lemmas.pow2_le_compat (64 * rLen) (64 * (j + 1)) }
    bn_v c + pow2 (64 * rLen) * bn_v n;
    (<) { }
    4 * bn_v n * bn_v n + pow2 (64 * rLen) * bn_v n;
    (<) { BL.mod_exp_mont_preconditions_rLen nLen (bn_v n);
      Math.Lemmas.lemma_mult_lt_right (bn_v n) (4 * bn_v n) (pow2 (64 * (nLen + 1))) }
    pow2 (64 * rLen) * bn_v n + pow2 (64 * rLen) * bn_v n;
    (==) { Math.Lemmas.pow2_plus 1 (64 * rLen) }
    pow2 (1 + 64 * rLen) * bn_v n;
    (<) { Math.Lemmas.lemma_mult_lt_left (pow2 (1 + 64 * rLen)) (bn_v n) (pow2 (64 * nLen)) }
    pow2 (1 + 64 * rLen) * pow2 (64 * nLen);
    (==) { Math.Lemmas.pow2_plus (1 + 64 * rLen) (64 * nLen) }
    pow2 (1 + 64 * rLen + 64 * nLen);
    (<) { Math.Lemmas.pow2_lt_compat (64 * rLen + 64 * rLen) (1 + 64 * rLen + 64 * nLen) }
    pow2 (128 * rLen);
  };
  assert (bn_v c + (pow2 (64 * (j + 1)) - 1) * bn_v n < pow2 (128 * rLen))


val mont_reduction_f_lemma_aux:
  nLen:nat -> resLen:nat{resLen == nLen + nLen + 2} -> a:nat -> b:nat -> c:nat -> j:nat{j <= nLen} -> Lemma
  (pow2 (64 * (nLen + j)) * (a + b - c * pow2 (64 * (resLen - j - nLen))) + pow2 (64 * resLen) * c ==
   pow2 (64 * (nLen + j)) * a + pow2 (64 * (nLen + j)) * b)
let mont_reduction_f_lemma_aux nLen resLen a b c j =
  calc (==) {
    pow2 (64 * (nLen + j)) * (a + b - c * pow2 (64 * (resLen - j - nLen)));
    (==) { Math.Lemmas.distributivity_sub_right (pow2 (64 * (nLen + j))) (a + b) (c * pow2 (64 * (resLen - j - nLen))) }
    pow2 (64 * (nLen + j)) * (a + b) - pow2 (64 * (nLen + j)) * c * pow2 (64 * (resLen - j - nLen));
    (==) { Math.Lemmas.distributivity_add_right (pow2 (64 * (nLen + j))) a b }
    pow2 (64 * (nLen + j)) * a + pow2 (64 * (nLen + j)) * b - pow2 (64 * (nLen + j)) * c * pow2 (64 * (resLen - j - nLen));
    (==) { Math.Lemmas.paren_mul_right (pow2 (64 * (nLen + j))) (pow2 (64 * (resLen - j - nLen))) c }
    pow2 (64 * (nLen + j)) * a + pow2 (64 * (nLen + j)) * b - pow2 (64 * (nLen + j)) * pow2 (64 * (resLen - j - nLen)) * c;
    (==) { Math.Lemmas.pow2_plus (64 * (nLen + j)) (64 * (resLen - nLen - j)) }
    pow2 (64 * (nLen + j)) * a + pow2 (64 * (nLen + j)) * b - pow2 (64 * resLen) * c;
  };
  assert (pow2 (64 * (nLen + j)) * (a + b - c * pow2 (64 * (resLen - j - nLen))) ==
    pow2 (64 * (nLen + j)) * a + pow2 (64 * (nLen + j)) * b - pow2 (64 * resLen) * c)


val mont_reduction_f_aux:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> j:size_nat{j < rLen}
  -> acc:lbignum (rLen + rLen) ->
  uint64 & lbignum (rLen + rLen)

let mont_reduction_f_aux #nLen #rLen n nInv_u64 j acc =
  let qj = nInv_u64 *. acc.[j] in
  let c, res1 = bn_mul_by_limb_add_shift_j #nLen #(rLen + rLen) n qj j acc in
  let res2 = slice res1 (j + nLen) (rLen + rLen) in
  let c1, res3 = bn_add res2 (create 1 c) in
  c1, update_sub res1 (j + nLen) (rLen + rLen - j - nLen) res3


val mont_reduction_f_aux_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> c:lbignum (rLen + rLen)
  -> j:size_nat{j < rLen}
  -> acc:lbignum (rLen + rLen) -> Lemma
   (let c1, res = mont_reduction_f_aux #nLen #rLen n mu j acc in
    let qj = mu *. acc.[j] in
    bn_v res + pow2 (128 * rLen) * v c1 == bn_v acc + bn_v n * v qj * pow2 (64 * j))

let mont_reduction_f_aux_lemma #nLen #rLen n mu c j acc =
  let resLen = rLen + rLen in
  let qj = mu *. acc.[j] in
  let c, res1 = bn_mul_by_limb_add_shift_j #nLen #resLen n qj j acc in
  bn_mul_by_limb_add_shift_j_lemma #nLen #(rLen+rLen) n qj j acc;
  assert (v c * pow2 (64 * (nLen + j)) + eval_ resLen res1 (nLen + j) == eval_ resLen acc (nLen + j) + bn_v n * v qj * pow2 (64 * j));

  let res2 = slice res1 (j + nLen) resLen in
  let acc2 = slice acc (j + nLen) resLen in
  assert (res1 == update_sub acc j nLen (snd (bn_mul_by_limb_add #nLen n qj (sub acc j nLen))));
  eq_intro res2 acc2;
  //assert (res2 == acc2);

  let c1, res3 = bn_add res2 (create 1 c) in
  bn_add_lemma res2 (create 1 c);
  bn_eval_create1 c;
  assert (v c1 * pow2 (64 * (resLen - j - nLen)) + bn_v res3 == bn_v acc2 + v c);

  let res4 = update_sub res1 (j + nLen) (resLen - j - nLen) res3 in
  calc (==) {
    bn_v res4 + pow2 (64 * resLen) * v c1;
    (==) { bn_eval_split_i res4 (j + nLen) }
    bn_v (slice res4 0 (j + nLen)) + pow2 (64 * (j + nLen)) * bn_v (slice res4 (j + nLen) resLen) + pow2 (64 * resLen) * v c1;
    (==) { }
    bn_v (slice res4 0 (j + nLen)) + pow2 (64 * (j + nLen)) * bn_v res3 + pow2 (64 * resLen) * v c1;
    (==) { eq_intro (sub res4 0 (j + nLen)) (sub res1 0 (j + nLen)) }
    bn_v (slice res1 0 (j + nLen)) + pow2 (64 * (j + nLen)) * bn_v res3 + pow2 (64 * resLen) * v c1;
    (==) { }
    bn_v (slice res1 0 (nLen + j)) + pow2 (64 * (nLen + j)) * (bn_v acc2 + v c - v c1 * pow2 (64 * (resLen - j - nLen))) + pow2 (64 * resLen) * v c1;
    (==) { bn_eval_extensionality_j res1 (slice res1 0 (nLen + j)) (nLen + j) }
    eval_ resLen res1 (nLen + j) + pow2 (64 * (nLen + j)) * (bn_v acc2 + v c - v c1 * pow2 (64 * (resLen - j - nLen))) + pow2 (64 * resLen) * v c1;
    (==) { }
    eval_ resLen acc (nLen + j) + bn_v n * v qj * pow2 (64 * j) - v c * pow2 (64 * (nLen + j)) +
      pow2 (64 * (nLen + j)) * (bn_v acc2 + v c - v c1 * pow2 (64 * (resLen - j - nLen))) + pow2 (64 * resLen) * v c1;
    (==) { mont_reduction_f_lemma_aux nLen resLen (bn_v acc2) (v c) (v c1) j }
    eval_ resLen acc (nLen + j) + bn_v n * v qj * pow2 (64 * j) + pow2 (64 * (nLen + j)) * bn_v acc2;
    (==) { bn_eval_extensionality_j acc (slice acc 0 (nLen + j)) (nLen + j) }
    bn_v (slice acc 0 (nLen + j)) + bn_v n * v qj * pow2 (64 * j) + pow2 (64 * (nLen + j)) * bn_v acc2;
    (==) { }
    bn_v (slice acc 0 (nLen + j)) + pow2 (64 * (nLen + j)) * bn_v acc2 + bn_v n * v qj * pow2 (64 * j);
    (==) { bn_eval_split_i acc (nLen + j) }
    bn_v acc + bn_v n * v qj * pow2 (64 * j);
  };
  assert (bn_v res4 + pow2 (64 * resLen) * v c1 == bn_v acc + bn_v n * v qj * pow2 (64 * j))


val mont_reduction_f_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> c:lbignum (rLen + rLen)
  -> j:size_nat{j < rLen}
  -> acc:lbignum (rLen + rLen) -> Lemma
  (requires
    0 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v c < 4 * bn_v n * bn_v n /\
    bn_v acc <= bn_v c + (pow2 (64 * j) - 1) * bn_v n)
  (ensures
   (let res = mont_reduction_ #nLen #rLen n mu j acc in
    bn_v res == bn_v acc + bn_v n * (v mu * v acc.[j] % pow2 64) * pow2 (64 * j) /\
    bn_v res <= bn_v c + (pow2 (64 * (j + 1)) - 1) * bn_v n))

let mont_reduction_f_lemma #nLen #rLen n mu c j acc =
  let c1, res = mont_reduction_f_aux #nLen #rLen n mu j acc in
  let qj = mu *. acc.[j] in
  mont_reduction_f_aux_lemma #nLen #rLen n mu c j acc;
  assert (bn_v res + pow2 (128 * rLen) * v c1 == bn_v acc + bn_v n * v qj * pow2 (64 * j));
  mont_reduction_f_lemma_bound #nLen #rLen n qj c j acc;
  assert (bn_v acc + bn_v n * v qj * pow2 (64 * j) < pow2 (128 * rLen));
  assert (v c1 = 0)


val mont_reduction_f_lemma_eq:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> c:lbignum (rLen + rLen)
  -> j:size_nat{j < rLen}
  -> acc:lbignum (rLen + rLen) -> Lemma
  (requires
    0 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v c < 4 * bn_v n * bn_v n /\
    bn_v acc <= bn_v c + (pow2 (64 * j) - 1) * bn_v n)
  (ensures
   (let res = mont_reduction_ #nLen #rLen n mu j acc in
    bn_v res == M.smont_reduction_f rLen (bn_v n) (v mu) j (bn_v acc) /\
    bn_v res <= bn_v c + (pow2 (64 * (j + 1)) - 1) * bn_v n))

let mont_reduction_f_lemma_eq #nLen #rLen n mu c j acc =
  let res = mont_reduction_ #nLen #rLen n mu j acc in
  mont_reduction_f_lemma #nLen #rLen n mu c j acc;
  bn_eval_index acc j;
  assert (v acc.[j] == bn_v acc / pow2 (64 * j) % pow2 64)


val mont_reduction_loop_lemma_eq:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen{bn_v n > 0}
  -> mu:uint64
  -> c:lbignum (rLen + rLen)
  -> j:size_nat{j <= rLen} -> Lemma
  (requires
    0 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v c < 4 * bn_v n * bn_v n)
  (ensures
   (let res = repeati j (mont_reduction_ #nLen #rLen n mu) c in
    bn_v res == repeati j (M.smont_reduction_f rLen (bn_v n) (v mu)) (bn_v c) /\
    bn_v res <= bn_v c + (pow2 (64 * j) - 1) * bn_v n))

let rec mont_reduction_loop_lemma_eq #nLen #rLen n mu c j =
  let res1 = repeati j (mont_reduction_ #nLen #rLen n mu) c in
  let res2 = repeati j (M.smont_reduction_f rLen (bn_v n) (v mu)) (bn_v c) in
  if j = 0 then begin
    eq_repeati0 j (mont_reduction_ #nLen #rLen n mu) c;
    eq_repeati0 j (M.smont_reduction_f rLen (bn_v n) (v mu)) (bn_v c) end
  else begin
    unfold_repeati j (mont_reduction_ #nLen #rLen n mu) c (j - 1);
    unfold_repeati j (M.smont_reduction_f rLen (bn_v n) (v mu)) (bn_v c) (j - 1);
    let res3 = repeati (j - 1) (mont_reduction_ #nLen #rLen n mu) c in
    let res4 = repeati (j - 1) (M.smont_reduction_f rLen (bn_v n) (v mu)) (bn_v c) in
    mont_reduction_loop_lemma_eq #nLen #rLen n mu c (j - 1);
    assert (bn_v res3 == res4);
    assert (res1 == mont_reduction_ #nLen #rLen n mu (j - 1) res3);
    assert (res2 == M.smont_reduction_f rLen (bn_v n) (v mu) (j - 1) res4);
    assert (bn_v res3 <= bn_v c + (pow2 (64 * (j - 1)) - 1) * bn_v n);
    mont_reduction_f_lemma_eq #nLen #rLen n mu c (j - 1) res3;
    assert (bn_v res1 == res2);
    () end


val mont_reduction_div_r_lemma:
  #rLen:size_nat{rLen + rLen <= max_size_t} -> c:lbignum (rLen + rLen) ->
  Lemma (bn_v (slice c rLen (rLen + rLen)) == bn_v c / pow2 (64 * rLen))
let mont_reduction_div_r_lemma #rLen c =
  calc (==) {
    bn_v c / pow2 (64 * rLen);
    (==) { bn_eval_split_i c rLen }
    (bn_v (slice c 0 rLen) + pow2 (64 * rLen) * bn_v (slice c rLen (rLen + rLen))) / pow2 (64 * rLen);
    (==) { Math.Lemmas.division_addition_lemma (bn_v (slice c 0 rLen)) (pow2 (64 * rLen)) (bn_v (slice c rLen (rLen + rLen))) }
    bn_v (slice c 0 rLen) / pow2 (64 * rLen) + bn_v (slice c rLen (rLen + rLen));
    (==) { bn_eval_bound (slice c 0 rLen) rLen; Math.Lemmas.small_division_lemma_1 (bn_v (slice c 0 rLen)) (pow2 (64 * rLen)) }
    bn_v (slice c rLen (rLen + rLen));
  };
  assert (bn_v (slice c rLen (rLen + rLen)) == bn_v c / pow2 (64 * rLen))


val mont_reduction:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> c:lbignum (rLen + rLen) ->
  lbignum rLen

let mont_reduction #nLen #rLen n nInv_u64 c =
  let c = repeati rLen (mont_reduction_ #nLen #rLen n nInv_u64) c in
  sub c rLen rLen


val to_mont:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> r2:lbignum nLen
  -> a:lbignum nLen ->
  aM:lbignum rLen

let to_mont #nLen #rLen n nInv_u64 r2 a =
  let c = bn_mul a r2 in // c = a * r2
  let tmp = create (rLen + rLen) (u64 0) in
  let tmp = update_sub tmp 0 (nLen + nLen) c in
  mont_reduction #nLen #rLen n nInv_u64 tmp // aM = c % n


val from_mont:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> aM:lbignum rLen ->
  a:lbignum nLen

let from_mont #nLen #rLen n nInv_u64 aM =
  let tmp = create (rLen + rLen) (u64 0) in
  let tmp = update_sub tmp 0 rLen aM in
  let a' = mont_reduction #nLen #rLen n nInv_u64 tmp in
  sub a' 0 nLen


val mul_mod_mont:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> aM:lbignum rLen
  -> bM:lbignum rLen ->
  resM:lbignum rLen

let mul_mod_mont #nLen #rLen n nInv_u64 aM bM =
  let c = bn_mul aM bM in // c = aM * bM
  mont_reduction n nInv_u64 c // resM = c % n


val mont_reduction_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> c:lbignum (rLen + rLen) -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v c < 4 * bn_v n * bn_v n)
  (ensures
    (let res = bn_v (mont_reduction #nLen #rLen n mu c) in
    res == M.mont_reduction rLen (bn_v n) (v mu) (bn_v c) /\
    res < 2 * bn_v n))

let mont_reduction_lemma #nLen #rLen n mu c =
  let res1 = repeati rLen (mont_reduction_ #nLen #rLen n mu) c in
  mont_reduction_loop_lemma_eq #nLen #rLen n mu c rLen;
  mont_reduction_div_r_lemma #rLen res1;
  assert (bn_v (mont_reduction #nLen #rLen n mu c) == M.mont_reduction rLen (bn_v n) (v mu) (bn_v c));
  let d, k = BL.eea_pow2_odd (64 * rLen) (bn_v n) in
  BL.mod_exp_mont_preconditions rLen (bn_v n) (v mu);
  BL.mod_exp_mont_preconditions_rLen nLen (bn_v n);
  M.mont_mult_lemma_fits rLen (bn_v n) d (v mu) (bn_v c)


val to_mont_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> r2:lbignum nLen
  -> a:lbignum nLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v a < bn_v n /\ bn_v r2 == pow2 (128 * rLen) % bn_v n)
  (ensures
   (let aM = bn_v (to_mont #nLen #rLen n mu r2 a) in
    aM == M.to_mont rLen (bn_v n) (v mu) (bn_v a) /\
    aM < 2 * bn_v n))

let to_mont_lemma #nLen #rLen n mu r2 a =
  assume (bn_v (to_mont #nLen #rLen n mu r2 a) == M.to_mont rLen (bn_v n) (v mu) (bn_v a));
  let d, k = BL.eea_pow2_odd (64 * rLen) (bn_v n) in
  BL.mod_exp_mont_preconditions rLen (bn_v n) (v mu);
  BL.mod_exp_mont_preconditions_rLen nLen (bn_v n);
  M.to_mont_lemma_fits rLen (bn_v n) d (v mu) (bn_v a)


val from_mont_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum rLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v aM < 2 * bn_v n)
  (ensures
   (let a = bn_v (from_mont #nLen #rLen n mu aM) in
    a == M.from_mont rLen (bn_v n) (v mu) (bn_v aM) /\
    a <= bn_v n))

let from_mont_lemma #nLen #rLen n mu aM =
  assume (bn_v (from_mont #nLen #rLen n mu aM) == M.from_mont rLen (bn_v n) (v mu) (bn_v aM));
  let d, k = BL.eea_pow2_odd (64 * rLen) (bn_v n) in
  BL.mod_exp_mont_preconditions rLen (bn_v n) (v mu);
  BL.mod_exp_mont_preconditions_rLen nLen (bn_v n);
  M.from_mont_lemma_fits rLen (bn_v n) d (v mu) (bn_v aM)

val mul_lt_lemma: a:nat -> b:nat -> c:pos -> Lemma
  (requires a < 2 * c /\ b < 2 * c)
  (ensures  a * b < 4 * c * c)
let mul_lt_lemma a b c = ()


val mul_mod_mont_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum rLen
  -> bM:lbignum rLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v aM < 2 * bn_v n /\ bn_v bM < 2 * bn_v n)
  (ensures
    (let res = bn_v (mul_mod_mont #nLen #rLen n mu aM bM) in
    res == M.mont_mul rLen (bn_v n) (v mu) (bn_v aM) (bn_v bM) /\
    res < 2 * bn_v n))

let mul_mod_mont_lemma #nLen #rLen n mu aM bM =
  let c = bn_mul aM bM in
  bn_mul_lemma aM bM;
  assert (bn_v c == bn_v aM * bn_v bM);
  mul_lt_lemma (bn_v aM) (bn_v bM) (bn_v n);
  assert (bn_v c < 4 * bn_v n * bn_v n);
  mont_reduction_lemma #nLen #rLen n mu c
