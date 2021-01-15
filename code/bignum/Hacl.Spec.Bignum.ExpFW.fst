module Hacl.Spec.Bignum.ExpFW

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module Loops = Lib.LoopCombinators
module LSeq = Lib.Sequence
module LE  = Lib.Exponentiation

module E = Hacl.Spec.Exponentiation.Lemmas
module M = Hacl.Spec.Montgomery.Lemmas

module BM = Hacl.Spec.Bignum.Montgomery
module BN = Hacl.Spec.Bignum
module BI = Hacl.Spec.Bignum.ModInvLimb
module BB = Hacl.Spec.Bignum.Base
module PT = Hacl.Spec.Bignum.PrecompTable

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val bn_mod_exp_pow2_mont:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> b:size_nat ->
  lbignum t nLen

let bn_mod_exp_pow2_mont #t #nLen n mu aM b =
  Loops.repeat b (BM.bn_mont_sqr n mu) aM


val bn_get_bits_l:
    #t:limb_t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> l:size_pos{l < bits t}
  -> i:nat{i < bBits / l} ->
  res:limb t{v res < pow2 l}

let bn_get_bits_l #t bBits bLen b l i =
  Math.Lemmas.lemma_mult_le_left l (i + 1) (bBits / l);
  assert (l * (i + 1) <= l * (bBits / l));
  Math.Lemmas.multiply_fractions bBits l;
  assert (l * (i + 1) <= bBits);
  let bits_l = BN.bn_get_bits b (bBits - l * i - l) l in
  BN.bn_get_bits_lemma b (bBits - l * i - l) l;
  assert (v bits_l < pow2 l);
  bits_l


val bn_mod_exp_fw_mont_f:
    #t:limb_t
  -> #nLen:size_pos
  -> n:lbignum t nLen
  -> mu:limb t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> l:size_pos{l < bits t}
  -> table_len:size_nat{1 < table_len /\ table_len * nLen <= max_size_t /\ table_len == pow2 l}
  -> table:lbignum t (table_len * nLen)
  -> i:nat{i < bBits / l}
  -> accM:lbignum t nLen ->
  lbignum t nLen

let bn_mod_exp_fw_mont_f #t #nLen n mu bBits bLen b l table_len table i accM =
  let acc_pow2l = bn_mod_exp_pow2_mont n mu accM l in
  let bits_l = bn_get_bits_l bBits bLen b l i in

  Math.Lemmas.lemma_mult_le_right nLen (v bits_l + 1) table_len;
  let a_powbits_l = sub table (v bits_l * nLen) nLen in
  BM.bn_mont_mul n mu acc_pow2l a_powbits_l


val bn_get_bits_c:
    #t:limb_t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> l:size_pos{l < bits t} ->
  res:limb t{v res < pow2 l}

let bn_get_bits_c #t bBits bLen b l =
  let c = bBits % l in
  let bits_c = BN.bn_get_bits b 0 c in
  BN.bn_get_bits_lemma b 0 c;
  Math.Lemmas.pow2_lt_compat l c;
  bits_c


val bn_mod_exp_fw_mont_rem:
    #t:limb_t
  -> #nLen:size_pos
  -> n:lbignum t nLen
  -> mu:limb t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> l:size_pos{l < bits t}
  -> table_len:size_nat{1 < table_len /\ table_len * nLen <= max_size_t /\ table_len == pow2 l}
  -> table:lbignum t (table_len * nLen)
  -> accM:lbignum t nLen ->
  lbignum t nLen

let bn_mod_exp_fw_mont_rem #t #nLen n mu bBits bLen b l table_len table accM =
  let c = bBits % l in
  let acc_pow2c = bn_mod_exp_pow2_mont n mu accM c in

  let bits_c = bn_get_bits_c #t bBits bLen b l in
  Math.Lemmas.lemma_mult_le_right nLen (v bits_c + 1) table_len;
  let a_powbits_c = sub table (v bits_c * nLen) nLen in
  BM.bn_mont_mul n mu acc_pow2c a_powbits_c


val bn_mod_exp_fw_mont_:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> l:size_pos{l < bits t /\ pow2 l * nLen <= max_size_t}
  -> r2:lbignum t nLen ->
  lbignum t nLen

let bn_mod_exp_fw_mont_ #t #nLen n mu aM bBits b l r2 =
  let bLen = blocks bBits (bits t) in
  let oneM = BM.bn_mont_one n mu r2 in

  let table_len = pow2 l in
  Math.Lemmas.pow2_le_compat l 1;
  assert (1 < table_len /\ table_len * nLen <= max_size_t);

  let table = PT.bn_mod_precomp_table_mont n mu table_len aM oneM in
  Math.Lemmas.multiply_fractions bBits l;
  let accM: lbignum t nLen = Loops.repeati (bBits / l) (bn_mod_exp_fw_mont_f n mu bBits bLen b l table_len table) oneM in
  let res = if bBits % l = 0 then accM else bn_mod_exp_fw_mont_rem n mu bBits bLen b l table_len table accM in
  res


let bn_mod_exp_fw_precompr2 #t nLen n a bBits b l r2 =
  let mu = BI.mod_inv_limb n.[0] in
  let aM = BM.bn_to_mont n mu r2 a in
  let resM = bn_mod_exp_fw_mont_ #t #nLen n mu aM bBits b l r2 in
  BM.bn_from_mont n mu resM


(* Lemmas *)

val bn_mod_exp_pow2_mont_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> b:size_nat -> Lemma
  (requires
    BM.bn_mont_pre n mu /\ bn_v aM < bn_v n)
  (ensures
   (let r = bn_mod_exp_pow2_mont #t #nLen n mu aM b in bn_v r < bn_v n /\
    bn_v r == E.mod_exp_pow2_mont (bits t) nLen (bn_v n) (v mu) (bn_v aM) b))

let rec bn_mod_exp_pow2_mont_lemma #t #nLen n mu aM b =
  if b = 0 then begin
    Loops.eq_repeat0 (BM.bn_mont_sqr n mu) aM;
    Loops.eq_repeat0 (M.mont_sqr (bits t) nLen (bn_v n) (v mu)) (bn_v aM);
    BM.bn_mont_sqr_lemma n mu aM end
  else begin
    let r1 = bn_mod_exp_pow2_mont n mu aM (b - 1) in
    Loops.unfold_repeat b (BM.bn_mont_sqr n mu) aM (b - 1);
    Loops.unfold_repeat b (M.mont_sqr (bits t) nLen (bn_v n) (v mu)) (bn_v aM) (b - 1);
    bn_mod_exp_pow2_mont_lemma #t #nLen n mu aM (b - 1);
    BM.bn_mont_sqr_lemma n mu r1;
    () end


val bn_get_bits_l_lemma:
    #t:limb_t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> l:size_pos{l < bits t}
  -> i:nat{i < bBits / l} -> Lemma
  (requires bn_v b < pow2 bBits)
  (ensures  v (bn_get_bits_l bBits bLen b l i) == LE.get_bits_l bBits (bn_v b) l i)

let bn_get_bits_l_lemma #t bBits bLen b l i =
  Math.Lemmas.lemma_mult_le_left l (i + 1) (bBits / l);
  assert (l * (i + 1) <= l * (bBits / l));
  Math.Lemmas.multiply_fractions bBits l;
  assert (l * (i + 1) <= bBits);
  let bits_l = BN.bn_get_bits b (bBits - l * i - l) l in
  BN.bn_get_bits_lemma b (bBits - l * i - l) l


val bn_mod_exp_fw_mont_f_lemma:
    #t:limb_t
  -> #nLen:size_pos
  -> n:lbignum t nLen
  -> mu:limb t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> l:size_pos{l < bits t}
  -> table_len:size_nat{1 < table_len /\ table_len * nLen <= max_size_t /\ table_len == pow2 l}
  -> oneM:lbignum t nLen
  -> aM:lbignum t nLen
  -> accM:lbignum t nLen
  -> i:nat{i < bBits / l} -> Lemma
  (requires
    BM.bn_mont_pre n mu /\ bn_v aM < bn_v n /\
    bn_v accM < bn_v n /\ bn_v b < pow2 bBits /\
    bn_v oneM == M.mont_one (bits t) nLen (bn_v n) (v mu) /\ bn_v oneM < bn_v n)
  (ensures
   (let t1 = PT.bn_mod_precomp_table_mont n mu table_len aM oneM in
    let t2 = E.mod_precomp_table_mont (bits t) nLen (bn_v n) (v mu) table_len (bn_v aM) in

    let r1 = bn_mod_exp_fw_mont_f n mu bBits bLen b l table_len t1 i accM in
    let r2 = E.mod_exp_fw_mont_f (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) l table_len t2 i (bn_v accM) in
    bn_v r1 == r2 /\ bn_v r1 < bn_v n))

let bn_mod_exp_fw_mont_f_lemma #t #nLen n mu bBits bLen b l table_len oneM aM accM i =
  let t1 = PT.bn_mod_precomp_table_mont n mu table_len aM oneM in
  let t2 = E.mod_precomp_table_mont (bits t) nLen (bn_v n) (v mu) table_len (bn_v aM) in

  let bits_l = bn_get_bits_l bBits bLen b l i in
  bn_get_bits_l_lemma bBits bLen b l i;
  assert (v bits_l < table_len);

  Math.Lemmas.lemma_mult_le_right nLen (v bits_l + 1) table_len;
  let a_powbits_l = sub t1 (v bits_l * nLen) nLen in
  PT.bn_mod_precomp_table_mont_lemma n mu table_len aM oneM (v bits_l);
  assert (bn_v a_powbits_l < bn_v n);

  let acc_pow2l = bn_mod_exp_pow2_mont n mu accM l in
  bn_mod_exp_pow2_mont_lemma n mu accM l;
  assert (bn_v acc_pow2l < bn_v n);

  let res = BM.bn_mont_mul n mu acc_pow2l a_powbits_l in
  BM.bn_mont_mul_lemma n mu acc_pow2l a_powbits_l


val bn_get_bits_c_lemma:
    #t:limb_t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> l:size_pos{l < bits t} -> Lemma
  (requires bn_v b < pow2 bBits)
  (ensures (let res = bn_get_bits_c bBits bLen b l in
    v res == bn_v b % pow2 (bBits % l) /\ v res < pow2 l))

let bn_get_bits_c_lemma #t bBits bLen b l =
  let c = bBits % l in
  let bits_c = bn_get_bits_c #t bBits bLen b l in
  BN.bn_get_bits_lemma b 0 c;
  assert_norm (pow2 0 = 1);
  assert (v bits_c == bn_v b % pow2 c)


val bn_mod_exp_fw_mont_rem_lemma:
    #t:limb_t
  -> #nLen:size_pos
  -> n:lbignum t nLen
  -> mu:limb t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> l:size_pos{l < bits t}
  -> table_len:size_nat{1 < table_len /\ table_len * nLen <= max_size_t /\ table_len == pow2 l}
  -> oneM:lbignum t nLen
  -> aM:lbignum t nLen
  -> accM:lbignum t nLen -> Lemma
  (requires
    BM.bn_mont_pre n mu /\ bn_v aM < bn_v n /\
    bn_v accM < bn_v n /\ bn_v b < pow2 bBits /\
    bn_v oneM == M.mont_one (bits t) nLen (bn_v n) (v mu) /\ bn_v oneM < bn_v n)
  (ensures
   (let t1 = PT.bn_mod_precomp_table_mont n mu table_len aM oneM in
    let t2 = E.mod_precomp_table_mont (bits t) nLen (bn_v n) (v mu) table_len (bn_v aM) in

    let r1 = bn_mod_exp_fw_mont_rem n mu bBits bLen b l table_len t1 accM in
    let r2 = E.mod_exp_fw_mont_rem (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) l table_len t2 (bn_v accM) in
    bn_v r1 == r2 /\ bn_v r1 < bn_v n))

let bn_mod_exp_fw_mont_rem_lemma #t #nLen n mu bBits bLen b l table_len oneM aM accM =
  let t1 = PT.bn_mod_precomp_table_mont n mu table_len aM oneM in
  let t2 = E.mod_precomp_table_mont (bits t) nLen (bn_v n) (v mu) table_len (bn_v aM) in

  let c = bBits % l in
  let acc_pow2c = bn_mod_exp_pow2_mont n mu accM c in
  bn_mod_exp_pow2_mont_lemma n mu accM c;
  assert (bn_v acc_pow2c < bn_v n);

  let bits_c = bn_get_bits_c #t bBits bLen b l in
  bn_get_bits_c_lemma #t bBits bLen b l;
  assert (v bits_c < table_len);

  Math.Lemmas.lemma_mult_le_right nLen (v bits_c + 1) table_len;
  let a_powbits_c = sub t1 (v bits_c * nLen) nLen in
  PT.bn_mod_precomp_table_mont_lemma n mu table_len aM oneM (v bits_c);
  assert (bn_v a_powbits_c < bn_v n);

  let res = BM.bn_mont_mul n mu acc_pow2c a_powbits_c in
  BM.bn_mont_mul_lemma n mu acc_pow2c a_powbits_c


val bn_mod_exp_fw_mont_loop_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> l:size_pos{l < bits t}
  -> table_len:size_nat{1 < table_len /\ table_len * nLen <= max_size_t /\ table_len == pow2 l}
  -> oneM:lbignum t nLen
  -> j:nat{j <= bBits / l} -> Lemma
  (requires
    BM.bn_mont_pre n mu /\ bn_v aM < bn_v n /\ bn_v b < pow2 bBits /\
    bn_v oneM == M.mont_one (bits t) nLen (bn_v n) (v mu) /\ bn_v oneM < bn_v n)
  (ensures
   (let t1 = PT.bn_mod_precomp_table_mont n mu table_len aM oneM in
    let t2 = E.mod_precomp_table_mont (bits t) nLen (bn_v n) (v mu) table_len (bn_v aM) in
    let bLen = blocks bBits (bits t) in

    let accM1 = Loops.repeati j (bn_mod_exp_fw_mont_f n mu bBits bLen b l table_len t1) oneM in
    let accM2 = Loops.repeati j (E.mod_exp_fw_mont_f (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) l table_len t2) (bn_v oneM) in
    bn_v accM1 == accM2 /\ bn_v accM1 < bn_v n))

let rec bn_mod_exp_fw_mont_loop_lemma #t #nLen n mu aM bBits b l table_len oneM j =
  let t1 = PT.bn_mod_precomp_table_mont n mu table_len aM oneM in
  let t2 = E.mod_precomp_table_mont (bits t) nLen (bn_v n) (v mu) table_len (bn_v aM) in
  let bLen = blocks bBits (bits t) in

  if j = 0 then begin
    Loops.eq_repeati0 j (bn_mod_exp_fw_mont_f n mu bBits bLen b l table_len t1) oneM;
    Loops.eq_repeati0 j (E.mod_exp_fw_mont_f (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) l table_len t2) (bn_v oneM) end
  else begin
    let accM3 = Loops.repeati (j - 1) (bn_mod_exp_fw_mont_f n mu bBits bLen b l table_len t1) oneM in
    let accM4 = Loops.repeati (j - 1) (E.mod_exp_fw_mont_f (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) l table_len t2) (bn_v oneM) in
    Loops.unfold_repeati j (E.mod_exp_fw_mont_f (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) l table_len t2) (bn_v oneM) (j - 1);
    Loops.unfold_repeati j (bn_mod_exp_fw_mont_f n mu bBits bLen b l table_len t1) oneM (j - 1);
    bn_mod_exp_fw_mont_loop_lemma n mu aM bBits b l table_len oneM (j - 1);
    bn_mod_exp_fw_mont_f_lemma #t #nLen n mu bBits bLen b l table_len oneM aM accM3 (j - 1);
    () end


val bn_mod_exp_fw_mont_aux_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> l:size_pos{l < bits t /\ pow2 l * nLen <= max_size_t}
  -> r2:lbignum t nLen -> Lemma
  (requires
    BM.bn_mont_pre n mu /\ bn_v aM < bn_v n /\ bn_v b < pow2 bBits /\
    bn_v r2 == pow2 (2 * bits t * nLen) % bn_v n)
  (ensures
   (let r1 = bn_mod_exp_fw_mont_ n mu aM bBits b l r2 in
    let r2 = E.mod_exp_fw_mont_ (bits t) nLen (bn_v n) (v mu) (bn_v aM) bBits (bn_v b) l in
    bn_v r1 == r2 /\ bn_v r1 < bn_v n))

let bn_mod_exp_fw_mont_aux_lemma #t #nLen n mu aM bBits b l r2 =
  let bLen = blocks bBits (bits t) in
  let oneM = BM.bn_mont_one n mu r2 in
  BM.bn_mont_one_lemma n mu r2;

  let table_len = pow2 l in
  Math.Lemmas.pow2_le_compat l 1;

  let table = PT.bn_mod_precomp_table_mont n mu table_len aM oneM in
  Math.Lemmas.multiply_fractions bBits l;
  let accM = Loops.repeati (bBits / l) (bn_mod_exp_fw_mont_f n mu bBits bLen b l table_len table) oneM in

  bn_mod_exp_fw_mont_loop_lemma n mu aM bBits b l table_len oneM (bBits / l);
  if bBits % l = 0 then ()
  else bn_mod_exp_fw_mont_rem_lemma n mu bBits bLen b l table_len oneM aM accM


let bn_mod_exp_fw_precompr2_lemma #t nLen n a bBits b l r2 =
  let mu = BI.mod_inv_limb n.[0] in
  BI.bn_mod_inv_limb_lemma n;

  let aM = BM.bn_to_mont n mu r2 a in
  BM.bn_to_mont_lemma n mu r2 a;

  let res1 = bn_mod_exp_fw_mont_ n mu aM bBits b l r2 in
  let res2 = E.mod_exp_fw_mont_ (bits t) nLen (bn_v n) (v mu) (bn_v aM) bBits (bn_v b) l in
  bn_mod_exp_fw_mont_aux_lemma n mu aM bBits b l r2;
  assert (bn_v res1 == res2 /\ bn_v res1 < bn_v n);

  let res = BM.bn_from_mont n mu res1 in
  BM.bn_from_mont_lemma n mu res1;

  bn_eval_bound n nLen;
  M.mont_preconditions (bits t) nLen (bn_v n) (v mu);
  E.mod_exp_fw_mont_lemma (bits t) nLen (bn_v n) (v mu) (bn_v a) bBits (bn_v b) l
