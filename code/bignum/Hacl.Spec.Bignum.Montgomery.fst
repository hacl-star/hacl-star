module Hacl.Spec.Bignum.Montgomery

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Definitions

module Loops = Lib.LoopCombinators
module BN = Hacl.Spec.Bignum

#reset-options "--z3rlimit 100 --fuel 0 --ifuel 0"

let bn_check_modulus #t #nLen n =
  let one = BN.bn_from_uint nLen (uint #t 1) in
  BN.bn_from_uint_lemma nLen (uint #t 1);
  let bit0 = BN.bn_is_odd n in
  BN.bn_is_odd_lemma n;
  assert (v bit0 == bn_v n % 2);
  let m0 = uint #t 0 -. bit0 in
  assert (v m0 == (if bn_v n % 2 = 1 then v (ones t SEC) else v (zeros t SEC)));

  let m1 = BN.bn_lt_mask one n in
  BN.bn_lt_mask_lemma one n;
  assert (v m1 == (if 1 < bn_v n then v (ones t SEC) else v (zeros t SEC)));
  let m = m0 &. m1 in
  logand_lemma m0 m1;
  assert (v m == (if bn_v n % 2 = 1 && 1 < bn_v n then v (ones t SEC) else v (zeros t SEC)));
  m


val bn_lshift1_mod_n: #t:limb_t -> #len:size_nat -> n:lbignum t len -> i:nat -> b:lbignum t len -> lbignum t len
let bn_lshift1_mod_n #t #len n i b = BN.bn_add_mod_n n b b

val bn_lshift1_mod_n_lemma: #t:limb_t -> #len:size_nat -> n:lbignum t len -> i:nat -> b:lbignum t len -> Lemma
  (requires 0 < bn_v n /\ bn_v b < bn_v n)
  (ensures  bn_v (bn_lshift1_mod_n n i b) == 2 * bn_v b % bn_v n)
let bn_lshift1_mod_n_lemma #t #len n i b =
  BN.bn_add_mod_n_lemma n b b

val bn_mul_by_pow2: #t:limb_t -> len:size_nat -> n:lbignum t len -> b:lbignum t len -> k:nat -> Lemma
  (requires 0 < bn_v n /\ bn_v b < bn_v n)
  (ensures  bn_v (Loops.repeati k (bn_lshift1_mod_n n) b) == pow2 k * bn_v b % bn_v n)
let rec bn_mul_by_pow2 #t len n b k =
  if k = 0 then Loops.eq_repeati0 k (bn_lshift1_mod_n n) b
  else begin
    let res = Loops.repeati k (bn_lshift1_mod_n n) b in
    let res0 = Loops.repeati (k - 1) (bn_lshift1_mod_n n) b in
    bn_mul_by_pow2 len n b (k - 1);
    assert (bn_v res0 == pow2 (k - 1) * bn_v b % bn_v n);
    Loops.unfold_repeati k (bn_lshift1_mod_n n) b (k - 1);
    assert (res == bn_lshift1_mod_n n (k - 1) res0);
    bn_lshift1_mod_n_lemma n (k - 1) res0;
    assert (bn_v res == 2 * (pow2 (k - 1) * bn_v b % bn_v n) % bn_v n);
    Math.Lemmas.lemma_mod_mul_distr_r 2 (pow2 (k - 1) * bn_v b) (bn_v n);
    assert (bn_v res == 2 * pow2 (k - 1) * bn_v b % bn_v n);
    Math.Lemmas.pow2_plus 1 (k - 1) end


let bn_precomp_r2_mod_n #t #nLen nBits n =
  let c = create nLen (uint #t 0) in
  let c0 = BN.bn_set_ith_bit c nBits in // c0 == pow2 nBits
  // pow2 (2 * bits t * nLen) / pow2 nBits == pow2 (2 * bits t * nLen - nBits)

  Loops.repeati (2 * bits t * nLen - nBits) (bn_lshift1_mod_n n) c0


let bn_precomp_r2_mod_n_lemma #t #nLen nBits n =
  let c = create nLen (uint #t 0) in
  let c0 = BN.bn_set_ith_bit c nBits in
  bn_eval_zeroes #t nLen nLen;
  BN.bn_set_ith_bit_lemma c nBits;
  assert (bn_v c0 == pow2 nBits);
  let res = Loops.repeati (2 * bits t * nLen - nBits) (bn_lshift1_mod_n n) c0 in
  bn_mul_by_pow2 nLen n c0 (2 * bits t * nLen - nBits);
  assert (bn_v res == pow2 (2 * bits t * nLen - nBits) * pow2 nBits % bn_v n);
  Math.Lemmas.pow2_plus (2 * bits t * nLen - nBits) nBits;
  assert (bn_v res == pow2 (2 * bits t * nLen) % bn_v n)


///  Low-level specification of Montgomery arithmetic

val bn_mont_reduction_f:
    #t:limb_t
  -> #nLen:size_nat{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> j:size_nat{j < nLen}
  -> tuple2 (carry t) (lbignum t (nLen + nLen)) ->
  tuple2 (carry t) (lbignum t (nLen + nLen))

let bn_mont_reduction_f #t #nLen n mu j (c0, acc) =
  let qj = mu *. acc.[j] in
  let c1, res1 = BN.bn_mul1_lshift_add n qj j acc in
  let c2, r = addcarry c0 c1 res1.[nLen + j] in
  let res = res1.[nLen + j] <- r in
  c2, res

let bn_mont_reduction_t (#t:limb_t) (#nLen:size_nat{nLen + nLen <= max_size_t}) (j:size_nat{j <= nLen}) =
  tuple2 (carry t) (lbignum t (nLen + nLen))


val bn_mont_reduction_loop_div_r:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> c:lbignum t (nLen + nLen) ->
  carry t & lbignum t nLen

let bn_mont_reduction_loop_div_r #t #nLen n mu c =
  let (c0, c) = Loops.repeat_gen nLen bn_mont_reduction_t (bn_mont_reduction_f n mu) (uint #t 0, c) in
  let res = BN.bn_rshift c nLen in
  c0, res


let bn_mont_reduction #t #nLen n mu c =
  let c0, res = bn_mont_reduction_loop_div_r #t #nLen n mu c in
  BN.bn_reduce_once n c0 res

let bn_to_mont #t #nLen n mu r2 a =
  let c = BN.bn_mul a r2 in // c = a * r2
  bn_mont_reduction n mu c // aM = c % n

let bn_from_mont #t #nLen n mu aM =
  let tmp = create (nLen + nLen) (uint #t 0) in
  let tmp = update_sub tmp 0 nLen aM in
  bn_mont_reduction n mu tmp

let bn_mont_mul #t #nLen n mu aM bM =
  let c = BN.bn_mul aM bM in // c = aM * bM
  bn_mont_reduction n mu c // resM = c % n

let bn_mont_sqr #t #nLen n mu aM =
  let c = BN.bn_mul aM aM in // c = aM * aM
  bn_mont_reduction n mu c // resM = c % n

let bn_mont_one #t #nLen n mu r2 =
  bn_from_mont n mu r2


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


val bn_mont_reduction_f_eval_lemma_aux:
  pbits:pos -> er0:nat -> rj:nat -> nLen:nat -> n:nat -> qj:nat -> j:nat -> c0:nat -> c1:nat -> c2:nat ->
  Lemma (let p = pow2 (pbits * (nLen + j)) in
    er0 + n * qj * pow2 (pbits * j) - c1 * p + p * (c0 + c1 + rj - c2 * pow2 pbits) ==
    er0 + n * qj * pow2 (pbits * j) + p * rj + p * c0 - pow2 (pbits * (nLen + j + 1)) * c2)

let bn_mont_reduction_f_eval_lemma_aux pbits er0 rj nLen n qj j c0 c1 c2 =
  let p = pow2 (pbits * (nLen + j)) in
  calc (==) {
    er0 + n * qj * pow2 (pbits * j) - c1 * p + p * (c0 + c1 + rj - c2 * pow2 pbits);
    (==) { Math.Lemmas.distributivity_add_right p c1 (c0 + rj - c2 * pow2 pbits) }
    er0 + n * qj * pow2 (pbits * j) - c1 * p + p * c1 + p * (c0 + rj - c2 * pow2 pbits);
    (==) { }
    er0 + n * qj * pow2 (pbits * j) + p * (c0 + rj - c2 * pow2 pbits);
    (==) { Math.Lemmas.distributivity_add_right p rj (c0 - c2 * pow2 pbits) }
    er0 + n * qj * pow2 (pbits * j) + p * rj + p * (c0 - c2 * pow2 pbits);
    (==) { Math.Lemmas.distributivity_sub_right p c0 (c2 * pow2 pbits); Math.Lemmas.paren_mul_right p c2 (pow2 pbits) }
    er0 + n * qj * pow2 (pbits * j) + p * rj + p * c0 - p * c2 * pow2 pbits;
    (==) { Math.Lemmas.pow2_plus (pbits * (nLen + j)) pbits; Math.Lemmas.paren_mul_right c2 p (pow2 pbits) }
    er0 + n * qj * pow2 (pbits * j) + p * rj + p * c0 - c2 * pow2 (pbits * (nLen + j + 1));
    }


val bn_mont_reduction_f_eval_lemma:
    #t:limb_t
  -> #nLen:size_nat{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> j:size_nat{j < nLen}
  -> cres0:tuple2 (carry t) (lbignum t (nLen + nLen)) ->
  Lemma (
    let (c0, res0) = cres0 in
    let (c2, res) = bn_mont_reduction_f n mu j (c0, res0) in
    let qj = mu *. res0.[j] in
    eval_ (nLen + nLen) res (nLen + j + 1) + v c2 * pow2 (bits t * (nLen + j + 1)) ==
    eval_ (nLen + nLen) res0 (nLen + j + 1) + bn_v n * v qj * pow2 (bits t * j) + v c0 * pow2 (bits t * (nLen + j)) /\
    slice res (nLen + j + 1) (nLen + nLen) == slice res0 (nLen + j + 1) (nLen + nLen))

let bn_mont_reduction_f_eval_lemma #t #nLen n mu j (c0, res0) =
  let pbits = bits t in
  let p = pow2 (pbits * (nLen + j)) in
  let resLen = nLen + nLen in
  let qj = mu *. res0.[j] in
  let c1, res1 = BN.bn_mul1_lshift_add n qj j res0 in
  BN.bn_mul1_lshift_add_lemma n qj j res0;
  assert (v c1 * p + eval_ resLen res1 (nLen + j) == eval_ resLen res0 (nLen + j) + bn_v n * v qj * pow2 (pbits * j));

  let c2, r = addcarry c0 c1 res1.[nLen + j] in
  assert (v r + v c2 * pow2 pbits == v c0 + v c1 + v res1.[nLen + j]);
  let res = res1.[nLen + j] <- r in
  bn_eval_extensionality_j res res1 (nLen + j);
  assert (eval_ resLen res (nLen + j) == eval_ resLen res1 (nLen + j));
  bn_eval_unfold_i res (nLen + j + 1);
  assert (eval_ resLen res (nLen + j + 1) == eval_ resLen res1 (nLen + j) + p * v res.[nLen + j]);

  calc (==) {
    eval_ resLen res1 (nLen + j) + p * v res.[nLen + j];
    (==) { }
    eval_ resLen res0 (nLen + j) + bn_v n * v qj * pow2 (pbits * j) - v c1 * p + p * (v c0 + v c1 + v res1.[nLen + j] - v c2 * pow2 pbits);
    (==) { bn_mont_reduction_f_eval_lemma_aux pbits (eval_ resLen res0 (nLen + j)) (v res1.[nLen + j]) nLen (bn_v n) (v qj) j (v c0) (v c1) (v c2) }
    eval_ resLen res0 (nLen + j) + p * v res1.[nLen + j] + bn_v n * v qj * pow2 (pbits * j) + p * v c0 - pow2 (pbits * (nLen + j + 1)) * v c2;
    (==) { Seq.lemma_index_slice res1 (nLen + j) resLen 0 }
    eval_ resLen res0 (nLen + j) + p * v res0.[nLen + j] + bn_v n * v qj * pow2 (pbits * j) + p * v c0 - pow2 (pbits * (nLen + j + 1)) * v c2;
    (==) { bn_eval_unfold_i res0 (nLen + j + 1) }
    eval_ resLen res0 (nLen + j + 1) + bn_v n * v qj * pow2 (pbits * j) + p * v c0 - pow2 (pbits * (nLen + j + 1)) * v c2;
  };

  eq_slice res0 res1 (nLen + j) (nLen + j + 1);
  eq_intro (slice res (nLen + j + 1) (nLen + nLen)) (slice res0 (nLen + j + 1) (nLen + nLen))


val bn_mont_reduction_f_lemma:
    #t:limb_t
  -> #nLen:size_nat{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> j:size_nat{j < nLen}
  -> cres0:tuple2 (carry t) (lbignum t (nLen + nLen)) ->
  Lemma (
    let (c0, res0) = cres0 in
    let (c2, res) = bn_mont_reduction_f n mu j (c0, res0) in
    let qj = mu *. res0.[j] in
    bn_v res + v c2 * pow2 (bits t * (nLen + j + 1)) ==
    bn_v res0 + bn_v n * v qj * pow2 (bits t * j) + v c0 * pow2 (bits t * (nLen + j)))

let bn_mont_reduction_f_lemma #t #nLen n mu j (c0, res0) =
  let (c2, res) = bn_mont_reduction_f n mu j (c0, res0) in
  bn_mont_reduction_f_eval_lemma n mu j (c0, res0);
  bn_eval_split_i res (nLen + j + 1);
  bn_eval_split_i res0 (nLen + j + 1);
  bn_eval_extensionality_j res (slice res 0 (nLen + j + 1)) (nLen + j + 1);
  bn_eval_extensionality_j res0 (slice res0 0 (nLen + j + 1)) (nLen + j + 1)


val bn_mont_reduction_loop_step_lemma:
    #t:limb_t
  -> #nLen:size_nat{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen{0 < bn_v n}
  -> mu:limb t
  -> j:size_nat{j < nLen}
  -> c1:carry t
  -> res1:lbignum t (nLen + nLen)
  -> resM1:nat -> Lemma
  (requires
    v c1 * pow2 (bits t * (nLen + j)) + bn_v res1 == resM1)
  (ensures
    (let (c2, res) = bn_mont_reduction_f n mu j (c1, res1) in
     let resM = M.mont_reduction_f (bits t) nLen (bn_v n) (v mu) j resM1 in
     v c2 * pow2 (bits t * (nLen + j + 1)) + bn_v res == resM))

let bn_mont_reduction_loop_step_lemma #t #nLen n mu j c1 res1 resM1 =
  let pbits = bits t in
  let (c2, res) = bn_mont_reduction_f n mu j (c1, res1) in
  let resM = M.mont_reduction_f pbits nLen (bn_v n) (v mu) j resM1 in
  bn_mont_reduction_f_lemma n mu j (c1, res1);
  let qj = mu *. res1.[j] in
  assert (bn_v res + v c2 * pow2 (pbits * (nLen + j + 1)) ==
    bn_v res1 + bn_v n * v qj * pow2 (pbits * j) + v c1 * pow2 (pbits * (nLen + j)));
  bn_eval_index res1 j;
  assert (v res1.[j] == bn_v res1 / pow2 (pbits * j) % pow2 pbits);
  assert (v qj == v mu * v res1.[j] % pow2 pbits);
  assert (bn_v res + v c2 * pow2 (pbits * (nLen + j + 1)) == resM1 + bn_v n * v qj * pow2 (pbits * j));
  let cjM = resM1 / pow2 (pbits * j) % pow2 pbits in
  let qjM = v mu * cjM % pow2 pbits in
  assert (resM == resM1 + bn_v n * qjM * pow2 (pbits * j));

  calc (==) {
    (v c1 * pow2 (pbits * (nLen + j)) + bn_v res1) / pow2 (pbits * j) % pow2 pbits;
    (==) { Math.Lemmas.pow2_plus (pbits * nLen) (pbits * j) }
    (v c1 * pow2 (pbits * nLen) * pow2 (pbits * j) + bn_v res1) / pow2 (pbits * j) % pow2 pbits;
    (==) { Math.Lemmas.division_addition_lemma (bn_v res1) (pow2 (pbits * j)) (v c1 * pow2 (pbits * nLen)) }
    (v c1 * pow2 (pbits * nLen) + bn_v res1 / pow2 (pbits * j)) % pow2 pbits;
    (==) { Math.Lemmas.pow2_plus (pbits * (nLen - 1)) pbits }
    (v c1 * pow2 (pbits * (nLen - 1)) * pow2 pbits + bn_v res1 / pow2 (pbits * j)) % pow2 pbits;
    (==) { Math.Lemmas.modulo_addition_lemma (bn_v res1 / pow2 (pbits * j)) (pow2 pbits) (v c1 * pow2 (pbits * (nLen - 1))) }
    (bn_v res1 / pow2 (pbits * j)) % pow2 pbits;
    }


val bn_mont_reduction_loop_lemma:
    #t:limb_t
  -> #nLen:size_nat{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen{0 < bn_v n}
  -> mu:limb t
  -> j:size_nat{j <= nLen}
  -> res0:lbignum t (nLen + nLen) ->
  Lemma (
    let (c2, res) = Loops.repeat_gen j bn_mont_reduction_t (bn_mont_reduction_f n mu) (uint #t 0, res0) in
    let resM = Loops.repeati j (M.mont_reduction_f (bits t) nLen (bn_v n) (v mu)) (bn_v res0) in
    v c2 * pow2 (bits t * (nLen + j)) + bn_v res == resM)

let rec bn_mont_reduction_loop_lemma #t #nLen n mu j res0 =
  let pbits = bits t in
  let (c2, res) = Loops.repeat_gen j bn_mont_reduction_t (bn_mont_reduction_f n mu) (uint #t 0, res0) in
  let resM = Loops.repeati j (M.mont_reduction_f pbits nLen (bn_v n) (v mu)) (bn_v res0) in

  if j = 0 then begin
    Loops.eq_repeati0 j (M.mont_reduction_f pbits nLen (bn_v n) (v mu)) (bn_v res0);
    Loops.eq_repeat_gen0 j bn_mont_reduction_t (bn_mont_reduction_f n mu) (uint #t 0, res0);
    () end
  else begin
    let (c1, res1) = Loops.repeat_gen (j - 1) bn_mont_reduction_t (bn_mont_reduction_f n mu) (uint #t 0, res0) in
    let resM1 = Loops.repeati (j - 1) (M.mont_reduction_f pbits nLen (bn_v n) (v mu)) (bn_v res0) in
    Loops.unfold_repeat_gen j bn_mont_reduction_t (bn_mont_reduction_f n mu) (uint #t 0, res0) (j - 1);
    assert ((c2, res) == bn_mont_reduction_f n mu (j - 1) (c1, res1));
    Loops.unfold_repeati j (M.mont_reduction_f pbits nLen (bn_v n) (v mu)) (bn_v res0) (j - 1);
    assert (resM == M.mont_reduction_f pbits nLen (bn_v n) (v mu) (j - 1) resM1);
    bn_mont_reduction_loop_lemma n mu (j - 1) res0;
    assert (v c1 * pow2 (pbits * (nLen + j - 1)) + bn_v res1 == resM1);
    bn_mont_reduction_loop_step_lemma n mu (j - 1) c1 res1 resM1;
    () end


val bn_mont_reduction_loop_div_r_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen{0 < bn_v n}
  -> mu:limb t
  -> c:lbignum t (nLen + nLen) ->
  Lemma
   (let (c2, res) = bn_mont_reduction_loop_div_r #t #nLen n mu c in
    let resM = M.mont_reduction_loop_div_r (bits t) nLen (bn_v n) (v mu) (bn_v c) in
    v c2 * pow2 (bits t * nLen) + bn_v res == resM)

let bn_mont_reduction_loop_div_r_lemma #t #nLen n mu res0 =
  let pbits = bits t in
  let r = pow2 (pbits * nLen) in
  let resLen = nLen + nLen in
  let (c0, res1) = Loops.repeat_gen nLen bn_mont_reduction_t (bn_mont_reduction_f n mu) (uint #t 0, res0) in
  let resM : nat = Loops.repeati nLen (M.mont_reduction_f pbits nLen (bn_v n) (v mu)) (bn_v res0) in
  bn_mont_reduction_loop_lemma n mu nLen res0;
  assert (v c0 * pow2 (pbits * resLen) + bn_v res1 == resM);
  let res2 = BN.bn_rshift res1 nLen in
  BN.bn_rshift_lemma res1 nLen;
  assert (bn_v res2 == bn_v res1 / r);

  calc (==) { // resM / r =
    (v c0 * pow2 (pbits * resLen) + bn_v res1) / r;
    (==) { Math.Lemmas.pow2_plus (pbits * nLen) (pbits * nLen) }
    (v c0 * r * r + bn_v res1) / r;
    (==) { Math.Lemmas.division_addition_lemma (bn_v res1) (r) (v c0 * r) }
    v c0 * r + bn_v res1 / r;
    (==) { }
    v c0 * r + bn_v res2;
    };
  assert (resM / r == v c0 * r + bn_v res2)


let bn_mont_reduction_lemma #t #nLen n mu res0 =
  let pbits = bits t in
  let r = pow2 (pbits * nLen) in
  let c0, res1 = bn_mont_reduction_loop_div_r #t #nLen n mu res0 in
  bn_mont_reduction_loop_div_r_lemma #t #nLen n mu res0;
  M.mont_reduction_loop_div_r_fits_lemma (bits t) nLen (bn_v n) (v mu) (bn_v res0);
  assert (v c0 * r + bn_v res1 <= (bn_v res0 - bn_v n) / r + bn_v n);
  M.lemma_fits_c_lt_rn (bn_v res0) r (bn_v n);
  assert (v c0 * r + bn_v res1 < 2 * bn_v n);

  let res2 = BN.bn_reduce_once n c0 res1 in
  BN.bn_reduce_once_lemma n c0 res1;
  assert (bn_v res2 == (v c0 * r + bn_v res1) % bn_v n);

  let resM = M.mont_reduction (bits t) nLen (bn_v n) (v mu) (bn_v res0) in
  let d, _ = M.eea_pow2_odd (pbits * nLen) (bn_v n) in
  M.mont_preconditions_d pbits nLen (bn_v n);
  M.mont_reduction_lemma (bits t) nLen (bn_v n) d (v mu) (bn_v res0);
  assert (resM == bn_v res0 * d % bn_v n);

  let resM1 = M.mont_reduction_loop_div_r (bits t) nLen (bn_v n) (v mu) (bn_v res0) in
  //assert (resM == (if resM1 < bn_v n then resM1 else resM1 - bn_v n));
  //assert (bn_v res2 == resM1 % bn_v n);
  if resM1 < bn_v n then begin
    //resM % bn_v n == resM1 % bn_v n ==> bn_v res2 == resM % bn_v
    Math.Lemmas.small_mod resM (bn_v n);
    assert (bn_v res2 == resM) end
  else begin
    //resM % bn_v n == (resM1 - bn_v n) % bn_v n == resM1 % bn_v n
    Math.Lemmas.lemma_mod_sub resM1 (bn_v n) 1;
    assert (resM % bn_v n == resM1 % bn_v n);
    Math.Lemmas.small_mod resM (bn_v n);
    assert (bn_v res2 == resM) end;
  assert (bn_v res2 == resM)


let bn_to_mont_lemma #t #nLen n mu r2 a =
  let r = pow2 (bits t * nLen) in
  let c = BN.bn_mul a r2 in // c = a * r2
  BN.bn_mul_lemma a r2;
  bn_eval_bound a nLen;
  M.mult_lt_lemma (bn_v a) (bn_v r2) r (bn_v n);
  assert (bn_v c < r * bn_v n);

  let aM = bn_mont_reduction n mu c in // aM = c % n
  bn_mont_reduction_lemma n mu c;
  assert (bn_v aM == M.mont_reduction (bits t) nLen (bn_v n) (v mu) (bn_v c))


let bn_from_mont_lemma #t #nLen n mu aM =
  let r = pow2 (bits t * nLen) in
  let tmp = create (nLen + nLen) (uint #t 0) in
  let tmp = update_sub tmp 0 nLen aM in
  bn_eval_update_sub nLen aM (nLen + nLen);
  assert (bn_v tmp == bn_v aM);
  bn_eval_bound aM nLen;
  assert (bn_v tmp < r);

  let a = bn_mont_reduction n mu tmp in
  bn_mont_reduction_lemma n mu tmp;
  assert (bn_v a == M.mont_reduction (bits t) nLen (bn_v n) (v mu) (bn_v tmp))


let bn_mont_mul_lemma #t #nLen n mu aM bM =
  let c = BN.bn_mul aM bM in
  BN.bn_mul_lemma aM bM;
  assert (bn_v c == bn_v aM * bn_v bM);
  Math.Lemmas.lemma_mult_lt_sqr (bn_v aM) (bn_v bM) (bn_v n);
  assert (bn_v c < bn_v n * bn_v n);
  bn_eval_bound n nLen;
  bn_mont_reduction_lemma n mu c


let bn_mont_sqr_lemma #t #nLen n mu aM =
  bn_mont_mul_lemma #t #nLen n mu aM aM


let bn_mont_one_lemma #t #nLen n mu r2 =
  bn_from_mont_lemma #t #nLen n mu r2
