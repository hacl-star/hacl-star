module Hacl.Spec.Bignum.Montgomery

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum

#reset-options "--z3rlimit 100 --fuel 0 --ifuel 0"

val bn_lshift1_mod_n: #len:size_nat -> n:lbignum len -> i:nat -> b:lbignum len -> lbignum len
let bn_lshift1_mod_n #len n i b = bn_add_mod_n n b b

val bn_lshift1_mod_n_lemma: #len:size_nat -> n:lbignum len -> i:nat -> b:lbignum len -> Lemma
  (requires 0 < bn_v n /\ bn_v b < bn_v n)
  (ensures  bn_v (bn_lshift1_mod_n n i b) == 2 * bn_v b % bn_v n)
let bn_lshift1_mod_n_lemma #len n i b =
  bn_add_mod_n_lemma n b b

val bn_mul_by_pow2: len:size_nat -> n:lbignum len -> b:lbignum len -> k:nat -> Lemma
  (requires 0 < bn_v n /\ bn_v b < bn_v n)
  (ensures  bn_v (repeati k (bn_lshift1_mod_n n) b) == pow2 k * bn_v b % bn_v n)
let rec bn_mul_by_pow2 len n b k =
  if k = 0 then eq_repeati0 k (bn_lshift1_mod_n n) b
  else begin
    let res = repeati k (bn_lshift1_mod_n n) b in
    let res0 = repeati (k - 1) (bn_lshift1_mod_n n) b in
    bn_mul_by_pow2 len n b (k - 1);
    assert (bn_v res0 == pow2 (k - 1) * bn_v b % bn_v n);
    unfold_repeati k (bn_lshift1_mod_n n) b (k - 1);
    assert (res == bn_lshift1_mod_n n (k - 1) res0);
    bn_lshift1_mod_n_lemma #len n (k - 1) res0;
    assert (bn_v res == 2 * (pow2 (k - 1) * bn_v b % bn_v n) % bn_v n);
    Math.Lemmas.lemma_mod_mul_distr_r 2 (pow2 (k - 1) * bn_v b) (bn_v n);
    assert (bn_v res == 2 * pow2 (k - 1) * bn_v b % bn_v n);
    Math.Lemmas.pow2_plus 1 (k - 1) end


let precomp_r2_mod_n #nLen modBits n =
  let c = create nLen (u64 0) in
  let c0 = bn_bit_set c (modBits - 1) in // c0 == pow2 (modBits - 1)
  // pow2 (128 * nLen) / pow2 (modBits - 1) == pow2 (128 * nLen + 1 - modBits)

  repeati (128 * nLen + 1 - modBits) (bn_lshift1_mod_n n) c0


let precomp_r2_mod_n_lemma #nLen modBits n =
  let c = create nLen (u64 0) in
  let c0 = bn_bit_set c (modBits - 1) in
  bn_eval_zeroes nLen nLen;
  bn_bit_set_lemma c (modBits - 1);
  assert (bn_v c0 == pow2 (modBits - 1));
  let res = repeati (128 * nLen + 1 - modBits) (bn_lshift1_mod_n n) c0 in
  bn_mul_by_pow2 nLen n c0 (128 * nLen + 1 - modBits);
  assert (bn_v res == pow2 (128 * nLen + 1 - modBits) * pow2 (modBits - 1) % bn_v n);
  Math.Lemmas.pow2_plus (128 * nLen + 1 - modBits) (modBits - 1);
  assert (bn_v res == pow2 (128 * nLen) % bn_v n)

///
///  Low-level specification of Montgomery arithmetic
///

val mont_reduction_f:
    #nLen:size_nat{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> j:size_nat{j < nLen}
  -> tuple2 carry (lbignum (nLen + nLen)) ->
  tuple2 carry (lbignum (nLen + nLen))

let mont_reduction_f #nLen n mu j (c0, acc) =
  let qj = mu *. acc.[j] in
  let c1, res1 = bn_mul1_lshift_add #nLen #(nLen + nLen) n qj j acc in
  let c2, r = addcarry_u64 c0 c1 res1.[nLen + j] in
  let res = res1.[nLen + j] <- r in
  c2, res

let mont_reduction_t (#nLen:size_nat{nLen + nLen <= max_size_t}) (j:size_nat{j <= nLen}) =
  tuple2 carry (lbignum (nLen + nLen))

let mont_reduction #nLen n mu c =
  let (c0, c) = repeat_gen nLen mont_reduction_t (mont_reduction_f #nLen n mu) (u64 0, c) in
  let res = bn_rshift c nLen in
  bn_reduce_once n c0 res

let to_mont #nLen n mu r2 a =
  //let c = bn_mul a r2 in // c = a * r2
  let c = bn_karatsuba_mul a r2 in
  mont_reduction #nLen n mu c // aM = c % n

let from_mont #nLen n mu aM =
  let tmp = create (nLen + nLen) (u64 0) in
  let tmp = update_sub tmp 0 nLen aM in
  mont_reduction #nLen n mu tmp

let mont_mul #nLen n mu aM bM =
  //let c = bn_mul aM bM in // c = aM * bM
  let c = bn_karatsuba_mul aM bM in
  mont_reduction n mu c // resM = c % n

let mont_sqr #nLen n mu aM =
  let c = bn_sqr aM in // c = aM * aM
  mont_reduction n mu c // resM = c % n


val eq_slice: #a:Type0 -> #len:size_nat -> b1:lseq a len -> b2:lseq a len -> i:nat -> j:nat{i <= j /\ j <= len} -> Lemma
  (requires slice b1 i len == slice b2 i len)
  (ensures  slice b1 j len == slice b2 j len)

let eq_slice #a #len b1 b2 i j =
  let aux (k:nat{k < len - j}) : Lemma (index (slice b1 j len) k == index (slice b2 j len) k) =
    Seq.lemma_index_slice b1 i len (k + j - i);
    Seq.lemma_index_slice b2 i len (k + j - i);
    () in

  Classical.forall_intro aux;
  eq_intro (slice b1 j len) (slice b2 j len)


val mont_reduction_f_eval_lemma:
    #nLen:size_nat{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> j:size_nat{j < nLen}
  -> cres0:tuple2 carry (lbignum (nLen + nLen)) ->
  Lemma (
    let (c0, res0) = cres0 in
    let (c2, res) = mont_reduction_f #nLen n mu j (c0, res0) in
    let qj = mu *. res0.[j] in
    eval_ (nLen + nLen) res (nLen + j + 1) + v c2 * pow2 (64 * (nLen + j + 1)) ==
    eval_ (nLen + nLen) res0 (nLen + j + 1) + bn_v n * v qj * pow2 (64 * j) + v c0 * pow2 (64 * (nLen + j)) /\
    slice res (nLen + j + 1) (nLen + nLen) == slice res0 (nLen + j + 1) (nLen + nLen))

let mont_reduction_f_eval_lemma #nLen n mu j (c0, res0) =
  let p = pow2 (64 * (nLen + j)) in
  let resLen = nLen + nLen in
  let qj = mu *. res0.[j] in
  let c1, res1 = bn_mul1_lshift_add #nLen #resLen n qj j res0 in
  bn_mul1_lshift_add_lemma #nLen #resLen n qj j res0;
  assert (v c1 * p + eval_ resLen res1 (nLen + j) == eval_ resLen res0 (nLen + j) + bn_v n * v qj * pow2 (64 * j));

  let c2, r = addcarry_u64 c0 c1 res1.[nLen + j] in
  assert (v r + v c2 * pow2 64 == v c0 + v c1 + v res1.[nLen + j]);
  let res = res1.[nLen + j] <- r in
  bn_eval_extensionality_j res res1 (nLen + j);
  assert (eval_ resLen res (nLen + j) == eval_ resLen res1 (nLen + j));
  bn_eval_unfold_i res (nLen + j + 1);
  assert (eval_ resLen res (nLen + j + 1) == eval_ resLen res1 (nLen + j) + p * v res.[nLen + j]);

  calc (==) {
    eval_ resLen res1 (nLen + j) + p * v res.[nLen + j];
    (==) { }
    eval_ resLen res0 (nLen + j) + bn_v n * v qj * pow2 (64 * j) - v c1 * p + p * (v c0 + v c1 + v res1.[nLen + j] - v c2 * pow2 64);
    (==) { Math.Lemmas.distributivity_add_right p (v c1) (v c0 + v res1.[nLen + j] - v c2 * pow2 64) }
    eval_ resLen res0 (nLen + j) + bn_v n * v qj * pow2 (64 * j) + p * (v c0 + v res1.[nLen + j] - v c2 * pow2 64);
    (==) { Math.Lemmas.distributivity_add_right p (v res1.[nLen + j]) (v c0 - v c2 * pow2 64) }
    eval_ resLen res0 (nLen + j) + bn_v n * v qj * pow2 (64 * j) + p * v res1.[nLen + j] + p * (v c0 - v c2 * pow2 64);
    (==) { Seq.lemma_index_slice res1 (nLen + j) resLen 0 }
    eval_ resLen res0 (nLen + j) + bn_v n * v qj * pow2 (64 * j) + p * v res0.[nLen + j] + p * (v c0 - v c2 * pow2 64);
    (==) { bn_eval_unfold_i res0 (nLen + j + 1) }
    eval_ resLen res0 (nLen + j + 1) + bn_v n * v qj * pow2 (64 * j) + p * (v c0 - v c2 * pow2 64);
    (==) { Math.Lemmas.distributivity_sub_right p (v c0) (v c2 * pow2 64) }
    eval_ resLen res0 (nLen + j + 1) + bn_v n * v qj * pow2 (64 * j) + p * v c0 - p * v c2 * pow2 64;
    (==) { Math.Lemmas.pow2_plus (64 * (nLen + j)) 64 }
    eval_ resLen res0 (nLen + j + 1) + bn_v n * v qj * pow2 (64 * j) + p * v c0 - pow2 (64 * (nLen + j + 1)) * v c2;
  };

  eq_slice res0 res1 (nLen + j) (nLen + j + 1);
  eq_intro (slice res (nLen + j + 1) (nLen + nLen)) (slice res0 (nLen + j + 1) (nLen + nLen))


val mont_reduction_f_lemma:
    #nLen:size_nat{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> j:size_nat{j < nLen}
  -> cres0:tuple2 carry (lbignum (nLen + nLen)) ->
  Lemma (
    let (c0, res0) = cres0 in
    let (c2, res) = mont_reduction_f #nLen n mu j (c0, res0) in
    let qj = mu *. res0.[j] in
    bn_v res + v c2 * pow2 (64 * (nLen + j + 1)) ==
    bn_v res0 + bn_v n * v qj * pow2 (64 * j) + v c0 * pow2 (64 * (nLen + j)))

let mont_reduction_f_lemma #nLen n mu j (c0, res0) =
  let (c2, res) = mont_reduction_f #nLen n mu j (c0, res0) in
  mont_reduction_f_eval_lemma #nLen n mu j (c0, res0);
  bn_eval_split_i res (nLen + j + 1);
  bn_eval_split_i res0 (nLen + j + 1);
  bn_eval_extensionality_j res (slice res 0 (nLen + j + 1)) (nLen + j + 1);
  bn_eval_extensionality_j res0 (slice res0 0 (nLen + j + 1)) (nLen + j + 1)


val mont_reduction_loop_step_lemma:
    #nLen:size_nat{nLen + nLen <= max_size_t}
  -> n:lbignum nLen{0 < bn_v n}
  -> mu:uint64
  -> j:size_nat{j < nLen}
  -> c1:carry
  -> res1:lbignum (nLen + nLen)
  -> resM1:nat -> Lemma
  (requires
    v c1 * pow2 (64 * (nLen + j)) + bn_v res1 == resM1)
  (ensures
    (let (c2, res) = mont_reduction_f #nLen n mu j (c1, res1) in
     let resM = M.mont_reduction_f nLen (bn_v n) (v mu) j resM1 in
     v c2 * pow2 (64 * (nLen + j + 1)) + bn_v res == resM))

let mont_reduction_loop_step_lemma #nLen n mu j c1 res1 resM1 =
  let (c2, res) = mont_reduction_f #nLen n mu j (c1, res1) in
  let resM = M.mont_reduction_f nLen (bn_v n) (v mu) j resM1 in
  mont_reduction_f_lemma #nLen n mu j (c1, res1);
  let qj = mu *. res1.[j] in
  assert (bn_v res + v c2 * pow2 (64 * (nLen + j + 1)) ==
    bn_v res1 + bn_v n * v qj * pow2 (64 * j) + v c1 * pow2 (64 * (nLen + j)));
  bn_eval_index res1 j;
  assert (v res1.[j] == bn_v res1 / pow2 (64 * j) % pow2 64);
  assert (v qj == v mu * v res1.[j] % pow2 64);
  assert (bn_v res + v c2 * pow2 (64 * (nLen + j + 1)) == resM1 + bn_v n * v qj * pow2 (64 * j));
  let cjM = resM1 / pow2 (64 * j) % pow2 64 in
  let qjM = v mu * cjM % pow2 64 in
  assert (resM == resM1 + bn_v n * qjM * pow2 (64 * j));

  calc (==) {
    (v c1 * pow2 (64 * (nLen + j)) + bn_v res1) / pow2 (64 * j) % pow2 64;
    (==) { Math.Lemmas.pow2_plus (64 * nLen) (64 * j) }
    (v c1 * pow2 (64 * nLen) * pow2 (64 * j) + bn_v res1) / pow2 (64 * j) % pow2 64;
    (==) { Math.Lemmas.division_addition_lemma (bn_v res1) (pow2 (64 * j)) (v c1 * pow2 (64 * nLen)) }
    (v c1 * pow2 (64 * nLen) + bn_v res1 / pow2 (64 * j)) % pow2 64;
    (==) { Math.Lemmas.pow2_plus (64 * (nLen - 1)) 64 }
    (v c1 * pow2 (64 * (nLen - 1)) * pow2 64 + bn_v res1 / pow2 (64 * j)) % pow2 64;
    (==) { Math.Lemmas.modulo_addition_lemma (bn_v res1 / pow2 (64 * j)) (pow2 64) (v c1 * pow2 (64 * (nLen - 1))) }
    (bn_v res1 / pow2 (64 * j)) % pow2 64;
    }


val mont_reduction_loop_lemma:
    #nLen:size_nat{nLen + nLen <= max_size_t}
  -> n:lbignum nLen{0 < bn_v n}
  -> mu:uint64
  -> j:size_nat{j <= nLen}
  -> res0:lbignum (nLen + nLen) ->
  Lemma (
    let (c2, res) = repeat_gen j mont_reduction_t (mont_reduction_f #nLen n mu) (u64 0, res0) in
    let resM = repeati j (M.mont_reduction_f nLen (bn_v n) (v mu)) (bn_v res0) in
    v c2 * pow2 (64 * (nLen + j)) + bn_v res == resM)

let rec mont_reduction_loop_lemma #nLen n mu j res0 =
  let (c2, res) = repeat_gen j mont_reduction_t (mont_reduction_f #nLen n mu) (u64 0, res0) in
  let resM = repeati j (M.mont_reduction_f nLen (bn_v n) (v mu)) (bn_v res0) in

  if j = 0 then begin
    eq_repeati0 j (M.mont_reduction_f nLen (bn_v n) (v mu)) (bn_v res0);
    eq_repeat_gen0 j mont_reduction_t (mont_reduction_f #nLen n mu) (u64 0, res0);
    () end
  else begin
    let (c1, res1) = repeat_gen (j - 1) mont_reduction_t (mont_reduction_f #nLen n mu) (u64 0, res0) in
    let resM1 = repeati (j - 1) (M.mont_reduction_f nLen (bn_v n) (v mu)) (bn_v res0) in
    unfold_repeat_gen j mont_reduction_t (mont_reduction_f #nLen n mu) (u64 0, res0) (j - 1);
    assert ((c2, res) == mont_reduction_f #nLen n mu (j - 1) (c1, res1));
    unfold_repeati j (M.mont_reduction_f nLen (bn_v n) (v mu)) (bn_v res0) (j - 1);
    assert (resM == M.mont_reduction_f nLen (bn_v n) (v mu) (j - 1) resM1);
    mont_reduction_loop_lemma #nLen n mu (j - 1) res0;
    assert (v c1 * pow2 (64 * (nLen + j - 1)) + bn_v res1 == resM1);
    mont_reduction_loop_step_lemma #nLen n mu (j - 1) c1 res1 resM1;
    () end


let mont_reduction_lemma #nLen n mu res0 =
  let resLen = nLen + nLen in
  let (c0, res1) = repeat_gen nLen mont_reduction_t (mont_reduction_f #nLen n mu) (u64 0, res0) in
  let resM : nat = repeati nLen (M.mont_reduction_f nLen (bn_v n) (v mu)) (bn_v res0) in
  mont_reduction_loop_lemma #nLen n mu nLen res0;
  assert (v c0 * pow2 (64 * resLen) + bn_v res1 == resM);
  let res2 = bn_rshift res1 nLen in
  bn_rshift_lemma res1 nLen;
  assert (bn_v res2 == bn_v res1 / pow2 (64 * nLen));

  calc (==) {
    (v c0 * pow2 (64 * resLen) + bn_v res1) / pow2 (64 * nLen);
    (==) { Math.Lemmas.pow2_plus (64 * nLen) (64 * nLen) }
    (v c0 * pow2 (64 * nLen) * pow2 (64 * nLen) + bn_v res1) / pow2 (64 * nLen);
    (==) { Math.Lemmas.division_addition_lemma (bn_v res1) (pow2 (64 * nLen)) (v c0 * pow2 (64 * nLen)) }
    v c0 * pow2 (64 * nLen) + bn_v res1 / pow2 (64 * nLen);
    (==) { }
    v c0 * pow2 (64 * nLen) + bn_v res2;
    };

  let d, k = M.eea_pow2_odd (64 * nLen) (bn_v n) in
  M.mont_preconditions nLen (bn_v n) (v mu);
  M.mont_mult_lemma_fits_aux nLen (bn_v n) (v mu) (bn_v res0);
  assert (resM / pow2 (64 * nLen) < 2 * bn_v n);

  let res3 = bn_reduce_once n c0 res2 in
  bn_reduce_once_lemma n c0 res2;
  assert (bn_v res3 == (v c0 * pow2 (64 * nLen) + bn_v res2) % bn_v n);

  let resM1 = resM / pow2 (64 * nLen) in
  let resM2 = if resM1 < bn_v n then resM1 else resM1 - bn_v n in
  Math.Lemmas.lemma_mod_sub resM1 (bn_v n) 1;
  assert (resM2 % bn_v n == resM1 % bn_v n);
  M.mont_mult_lemma_fits nLen (bn_v n) (v mu) (bn_v res0);
  Math.Lemmas.small_mod resM2 (bn_v n);
  assert (resM2 == resM1 % bn_v n)


let to_mont_lemma #nLen n mu r2 a =
  let c = bn_karatsuba_mul a r2 in // c = a * r2
  bn_karatsuba_mul_lemma a r2;
  Math.Lemmas.lemma_mult_lt_sqr (bn_v a) (bn_v r2) (bn_v n);
  assert (bn_v c < bn_v n * bn_v n);

  let aM = mont_reduction #nLen n mu c in // aM = c % n
  mont_reduction_lemma #nLen n mu c;
  assert (bn_v aM == M.mont_reduction nLen (bn_v n) (v mu) (bn_v c))


let from_mont_lemma #nLen n mu aM =
  let tmp = create (nLen + nLen) (u64 0) in
  let tmp = update_sub tmp 0 nLen aM in
  bn_eval_update_sub nLen aM (nLen + nLen);
  assert (bn_v tmp == bn_v aM);

  let a = mont_reduction #nLen n mu tmp in
  mont_reduction_lemma n mu tmp;
  assert (bn_v a == M.mont_reduction nLen (bn_v n) (v mu) (bn_v tmp))


let mont_mul_lemma #nLen n mu aM bM =
  let c = bn_karatsuba_mul aM bM in
  bn_karatsuba_mul_lemma aM bM;
  assert (bn_v c == bn_v aM * bn_v bM);
  Math.Lemmas.lemma_mult_lt_sqr (bn_v aM) (bn_v bM) (bn_v n);
  assert (bn_v c < bn_v n * bn_v n);
  mont_reduction_lemma #nLen n mu c


let mont_sqr_lemma #nLen n mu aM =
  let c = bn_sqr aM in
  bn_sqr_lemma aM;
  assert (bn_v c == bn_v aM * bn_v aM);
  Math.Lemmas.lemma_mult_lt_sqr (bn_v aM) (bn_v aM) (bn_v n);
  assert (bn_v c < bn_v n * bn_v n);
  mont_reduction_lemma #nLen n mu c
