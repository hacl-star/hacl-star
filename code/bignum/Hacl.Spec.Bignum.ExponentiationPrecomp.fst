module Hacl.Spec.Bignum.ExponentiationPrecomp

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module Loops = Lib.LoopCombinators
module LSeq = Lib.Sequence

module E = Hacl.Spec.Exponentiation.Lemmas
module M = Hacl.Spec.Montgomery.Lemmas

module BE = Hacl.Spec.Bignum.Exponentiation
module BM = Hacl.Spec.Bignum.Montgomery
module BN = Hacl.Spec.Bignum
module BI = Hacl.Spec.Bignum.ModInvLimb

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val bn_mod_exp_mont_pow2:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> b:size_nat ->
  lbignum t nLen

let bn_mod_exp_mont_pow2 #t #nLen n mu aM b =
  Loops.repeat b (BM.bn_mont_sqr n mu) aM


val bn_mod_exp_mont_pow2_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> b:size_nat -> Lemma
  (requires
    BM.bn_mont_pre n mu /\ bn_v aM < bn_v n)
  (ensures
   (let r = bn_mod_exp_mont_pow2 #t #nLen n mu aM b in bn_v r < bn_v n /\
    bn_v r == E.mod_exp_mont_pow2 (bits t) nLen (bn_v n) (v mu) (bn_v aM) b))

let rec bn_mod_exp_mont_pow2_lemma #t #nLen n mu aM b =
  if b = 0 then begin
    Loops.eq_repeat0 (BM.bn_mont_sqr n mu) aM;
    Loops.eq_repeat0 (M.mont_sqr (bits t) nLen (bn_v n) (v mu)) (bn_v aM);
    BM.bn_mont_sqr_lemma n mu aM end
  else begin
    let r1 = bn_mod_exp_mont_pow2 #t #nLen n mu aM (b - 1) in
    Loops.unfold_repeat b (BM.bn_mont_sqr n mu) aM (b - 1);
    Loops.unfold_repeat b (M.mont_sqr (bits t) nLen (bn_v n) (v mu)) (bn_v aM) (b - 1);
    bn_mod_exp_mont_pow2_lemma #t #nLen n mu aM (b - 1);
    BM.bn_mont_sqr_lemma n mu r1;
    () end


val bn_mod_exp_mont_precomp_table_f:
    #t:limb_t
  -> #nLen:size_pos
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> table_len:size_nat{1 < table_len /\ table_len * nLen <= max_size_t}
  -> i:nat{i < table_len - 2}
  -> table:lbignum t (table_len * nLen) ->
  lbignum t (table_len * nLen)

let bn_mod_exp_mont_precomp_table_f #t #nLen n mu aM table_len i table =
  let t1 = sub table ((i + 1) * nLen) nLen in
  let r = BM.bn_mont_mul n mu t1 aM in
  update_sub table ((i + 2) * nLen) nLen r


val bn_mod_exp_mont_precomp_table:
    #t:limb_t
  -> #nLen:size_pos
  -> n:lbignum t nLen
  -> mu:limb t
  -> table_len:size_nat{1 < table_len /\ table_len * nLen <= max_size_t}
  -> aM:lbignum t nLen
  -> oneM:lbignum t nLen ->
  lbignum t (table_len * nLen)

let bn_mod_exp_mont_precomp_table #t #nLen n mu table_len aM oneM =
  let table = create (table_len * nLen) (uint #t 0) in
  let table = update_sub table 0 nLen oneM in
  let table = update_sub table nLen nLen aM in

  Loops.repeati (table_len - 2) (bn_mod_exp_mont_precomp_table_f n mu aM table_len) table


val bn_mod_exp_mont_precomp_table_loop_lemma:
    #t:limb_t
  -> #nLen:size_pos
  -> n:lbignum t nLen
  -> mu:limb t
  -> table_len:size_nat{1 < table_len /\ table_len * nLen <= max_size_t}
  -> aM:lbignum t nLen
  -> t01:lbignum t (table_len * nLen)
  -> t02:lseq nat table_len
  -> j:nat{j <= table_len - 2} -> Lemma
  (requires
    BM.bn_mont_pre n mu /\ bn_v aM < bn_v n /\
    index t02 0 == bn_v (sub t01 0 nLen) /\
    index t02 1 == bn_v (sub t01 nLen nLen))
  (ensures
   (let t3 : lbignum t (table_len * nLen) = Loops.repeati j (bn_mod_exp_mont_precomp_table_f n mu aM table_len) t01 in
    let t4 : lseq nat table_len = Loops.repeati j
      (E.mod_exp_mont_precomp_table_f (bits t) nLen (bn_v n) (v mu) (bn_v aM) table_len) t02 in
    (forall (i:nat{i < j + 2}).
     (Math.Lemmas.lemma_mult_le_right nLen (i + 1) (table_len);
      assert (i * nLen + nLen <= table_len * nLen);
      let bi = sub t3 (i * nLen) nLen in bn_v bi == index t4 i))))

let bn_mod_exp_mont_precomp_table_loop_lemma #t #nLen n mu table_len aM t01 t02 j =
  admit()


val bn_mod_exp_mont_precomp_table_lemma:
    #t:limb_t
  -> #nLen:size_pos
  -> n:lbignum t nLen
  -> mu:limb t
  -> table_len:size_nat{1 < table_len /\ table_len * nLen <= max_size_t}
  -> aM:lbignum t nLen
  -> oneM:lbignum t nLen -> Lemma
  (requires
    BM.bn_mont_pre n mu /\ bn_v aM < bn_v n /\
    bn_v oneM == M.to_mont (bits t) nLen (bn_v n) (v mu) 1)
  (ensures
   (let t1 : lbignum t (table_len * nLen) = bn_mod_exp_mont_precomp_table n mu table_len aM oneM in
    let t2 : lseq nat table_len = E.mod_exp_mont_precomp_table (bits t) nLen (bn_v n) (v mu) table_len (bn_v aM) in
    (forall (i:nat{i < table_len}).
     (Math.Lemmas.lemma_mult_le_right nLen (i + 1) (table_len);
      assert (i * nLen + nLen <= table_len * nLen);
      let bi = sub t1 (i * nLen) nLen in bn_v bi == index t2 i))))

let bn_mod_exp_mont_precomp_table_lemma #t #nLen n mu table_len aM oneM =
  let t01 = create (table_len * nLen) (uint #t 0) in
  let t01' = update_sub t01 0 nLen oneM in
  let t01 = update_sub t01' nLen nLen aM in

  let t02 = create table_len 0 in
  let t02' = t02.[0] <- bn_v oneM in
  let t02 = t02'.[1] <- bn_v aM in
  LSeq.eq_intro (sub t01 0 nLen) (sub t01' 0 nLen);
  assert (index t02 0 == bn_v (sub t01 0 nLen));
  assert (index t02 1 == bn_v (sub t01 nLen nLen));
  bn_mod_exp_mont_precomp_table_loop_lemma #t #nLen n mu table_len aM t01 t02 (table_len - 2)


val bn_mod_exp_mont_precomp_f:
    #t:limb_t
  -> #nLen:size_pos
  -> n:lbignum t nLen
  -> mu:limb t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> l:size_nat{l <= bits t}
  -> table_len:size_nat{1 < table_len /\ table_len * nLen <= max_size_t /\ table_len == pow2 l}
  -> table:lbignum t (table_len * nLen)
  -> i:nat{l * (i + 1) <= bBits}
  -> accM:lbignum t nLen ->
  lbignum t nLen

let bn_mod_exp_mont_precomp_f #t #nLen n mu bBits bLen b l table_len table i accM =
  let bits_l = BN.bn_get_bits b (bBits - l * i - l) l in
  BN.bn_get_bits_lemma b (bBits - l * i - l) l;
  assert (v bits_l < table_len);
  let acc_pow2l = bn_mod_exp_mont_pow2 n mu accM l in
  Math.Lemmas.lemma_mult_le_right nLen (v bits_l + 1) table_len;
  let a_powbits_l = sub table (v bits_l * nLen) nLen in
  BM.bn_mont_mul n mu acc_pow2l a_powbits_l


#set-options "--z3rlimit 150"
val bn_mod_exp_mont_precomp_f_lemma:
    #t:limb_t
  -> #nLen:size_pos
  -> n:lbignum t nLen
  -> mu:limb t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> l:size_nat{l <= bits t}
  -> table_len:size_nat{1 < table_len /\ table_len * nLen <= max_size_t /\ table_len == pow2 l}
  -> t1:lbignum t (table_len * nLen)
  -> t2:lseq nat table_len
  -> oneM:lbignum t nLen
  -> aM:lbignum t nLen
  -> i:nat{l * (i + 1) <= bBits}
  -> accM:lbignum t nLen -> Lemma
  (requires
    BM.bn_mont_pre n mu /\ bn_v aM < bn_v n /\
    bn_v accM < bn_v n /\ bn_v b < pow2 bBits /\
    bn_v oneM == M.to_mont (bits t) nLen (bn_v n) (v mu) 1 /\
    t1 == bn_mod_exp_mont_precomp_table n mu table_len aM oneM /\
    t2 == E.mod_exp_mont_precomp_table (bits t) nLen (bn_v n) (v mu) table_len (bn_v aM))
  (ensures
   (let r1 = bn_mod_exp_mont_precomp_f n mu bBits bLen b l table_len t1 i accM in
    let r2 = E.mod_exp_mont_precomp_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) l table_len t2 i (bn_v accM) in
    bn_v r1 == r2))

let bn_mod_exp_mont_precomp_f_lemma #t #nLen n mu bBits bLen b l table_len t1 t2 oneM aM i accM =
  let bits_l = BN.bn_get_bits b (bBits - l * i - l) l in
  BN.bn_get_bits_lemma b (bBits - l * i - l) l;
  assert (v bits_l == bn_v b / pow2 (bBits - l * i - l) % table_len);
  assert (v bits_l < table_len);
  let acc_pow2l = bn_mod_exp_mont_pow2 n mu accM l in
  bn_mod_exp_mont_pow2_lemma n mu accM l;
  bn_eval_bound n nLen;
  M.mont_preconditions (bits t) nLen (bn_v n) (v mu);
  E.mod_exp_mont_pow2_lemma (bits t) nLen (bn_v n) (v mu) (bn_v accM) l;
  assert (bn_v acc_pow2l < bn_v n);

  Math.Lemmas.lemma_mult_le_right nLen (v bits_l + 1) table_len;
  let a_powbits_l = sub t1 (v bits_l * nLen) nLen in
  bn_mod_exp_mont_precomp_table_lemma n mu table_len aM oneM;
  E.mod_exp_mont_precomp_table_lemma (bits t) nLen (bn_v n) (v mu) table_len (bn_v aM) (v bits_l);
  assert (bn_v a_powbits_l < bn_v n);

  let res = BM.bn_mont_mul n mu acc_pow2l a_powbits_l in
  BM.bn_mont_mul_lemma n mu acc_pow2l a_powbits_l


// val bn_mod_exp_mont_precomp_loop_lemma:
//     #t:limb_t
//   -> #nLen:size_pos
//   -> n:lbignum t nLen
//   -> mu:limb t
//   -> bBits:size_pos
//   -> bLen:size_nat{bLen == blocks bBits (bits t)}
//   -> b:lbignum t bLen
//   -> l:size_pos{l <= bits t}
//   -> table_len:size_nat{1 < table_len /\ table_len * nLen <= max_size_t /\ table_len == pow2 l}
//   -> t1:lbignum t (table_len * nLen)
//   -> t2:lseq nat table_len
//   -> oneM:lbignum t nLen
//   -> aM:lbignum t nLen
//   -> j:nat{j <= bBits / l}
//   -> accM:lbignum t nLen -> Lemma
//   (requires
//     BM.bn_mont_pre n mu /\ E.mont_pre (bits t) nLen (bn_v n) (v mu) /\
//     bn_v aM < bn_v n /\ bn_v accM < bn_v n /\ bn_v b < pow2 bBits /\
//     bn_v oneM == M.to_mont (bits t) nLen (bn_v n) (v mu) 1 /\
//     t1 == bn_mod_exp_mont_precomp_table n mu table_len aM oneM /\
//     t2 == E.mod_exp_mont_precomp_table (bits t) nLen (bn_v n) (v mu) table_len (bn_v aM))
//   (ensures
//    (Math.Lemmas.multiply_fractions bBits l;
//     Math.Lemmas.lemma_mult_le_left l j (bBits / l);
//     assert (l * (bBits / l) <= bBits);
//     let r1 : lbignum t nLen = Loops.repeati j (bn_mod_exp_mont_precomp_f n mu bBits bLen b l table_len t1) accM in
//     let r2 = Loops.repeati j (E.mod_exp_mont_precomp_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) l table_len t2) (bn_v accM) in
//     bn_v r1 == r2))

// let rec bn_mod_exp_mont_precomp_loop_lemma #t #nLen n mu bBits bLen b l table_len t1 t2 oneM aM j accM =
//   Math.Lemmas.multiply_fractions bBits l;
//   Math.Lemmas.lemma_mult_le_left l j (bBits / l);
//   assert (l * (bBits / l) <= bBits);
//   let r1 : lbignum t nLen = Loops.repeati j (bn_mod_exp_mont_precomp_f n mu bBits bLen b l table_len t1) accM in
//   let r2 = Loops.repeati j (E.mod_exp_mont_precomp_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) l table_len t2) (bn_v accM) in

//   if j = 0 then begin
//     Loops.eq_repeati0 j (bn_mod_exp_mont_precomp_f n mu bBits bLen b l table_len t1) accM;
//     Loops.eq_repeati0 j (E.mod_exp_mont_precomp_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) l table_len t2) (bn_v accM) end
//   else begin
//     //let r3 = Loops.repeati (j - 1) (bn_mod_exp_mont_precomp_f n mu bBits bLen b l table_len t1) accM in
//     //Loops.unfold_repeati j (bn_mod_exp_mont_precomp_f n mu bBits bLen b l table_len t1) accM (j - 1);
//     //Loops.unfold_repeati j (E.mod_exp_mont_precomp_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) l table_len t2) (bn_v accM) (j - 1);
//     //bn_mod_exp_mont_precomp_loop_lemma n mu bBits bLen b l table_len t1 t2 oneM aM (j - 1) accM;
//     //bn_mod_exp_mont_precomp_f_lemma n mu bBits bLen b l table_len t1 t2 oneM aM (j - 1) r3;
//     admit() end



val bn_mod_exp_mont_precomp_rem:
    #t:limb_t
  -> #nLen:size_pos
  -> n:lbignum t nLen
  -> mu:limb t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> l:size_pos{l <= bits t}
  -> table_len:size_nat{1 < table_len /\ table_len * nLen <= max_size_t /\ table_len == pow2 l}
  -> table:lbignum t (table_len * nLen)
  -> accM:lbignum t nLen ->
  lbignum t nLen

let bn_mod_exp_mont_precomp_rem #t #nLen n mu bBits bLen b l table_len table accM =
  let c = bBits % l in
  let bits_c = BN.bn_get_bits b 0 c in
  BN.bn_get_bits_lemma b 0 c;
  let acc_pow2c = bn_mod_exp_mont_pow2 n mu accM c in
  Math.Lemmas.pow2_lt_compat l c;
  Math.Lemmas.lemma_mult_le_right nLen (v bits_c + 1) table_len;
  let a_powbits_c = sub table (v bits_c * nLen) nLen in
  BM.bn_mont_mul n mu acc_pow2c a_powbits_c


val bn_mod_exp_mont_precomp_rem_lemma:
    #t:limb_t
  -> #nLen:size_pos
  -> n:lbignum t nLen
  -> mu:limb t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> l:size_pos{l <= bits t}
  -> table_len:size_nat{1 < table_len /\ table_len * nLen <= max_size_t /\ table_len == pow2 l}
  -> t1:lbignum t (table_len * nLen)
  -> t2:lseq nat table_len
  -> oneM:lbignum t nLen
  -> aM:lbignum t nLen
  -> accM:lbignum t nLen -> Lemma
  (requires
    BM.bn_mont_pre n mu /\ bn_v aM < bn_v n /\
    bn_v accM < bn_v n /\ bn_v b < pow2 bBits /\
    bn_v oneM == M.to_mont (bits t) nLen (bn_v n) (v mu) 1 /\
    t1 == bn_mod_exp_mont_precomp_table n mu table_len aM oneM /\
    t2 == E.mod_exp_mont_precomp_table (bits t) nLen (bn_v n) (v mu) table_len (bn_v aM))
  (ensures
   (let r1 = bn_mod_exp_mont_precomp_rem n mu bBits bLen b l table_len t1 accM in
    let r2 = E.mod_exp_mont_precomp_rem_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) l table_len t2 (bn_v accM) in
    bn_v r1 == r2))


let bn_mod_exp_mont_precomp_rem_lemma #t #nLen n mu bBits bLen b l table_len t1 t2 oneM aM accM =
  let c = bBits % l in
  let bits_c = BN.bn_get_bits b 0 c in
  BN.bn_get_bits_lemma b 0 c;
  assert_norm (pow2 0 = 1);
  assert (v bits_c == bn_v b % pow2 c);
  Math.Lemmas.pow2_lt_compat l c;
  assert (v bits_c < table_len);

  let acc_pow2c = bn_mod_exp_mont_pow2 n mu accM c in
  bn_mod_exp_mont_pow2_lemma n mu accM c;
  bn_eval_bound n nLen;
  M.mont_preconditions (bits t) nLen (bn_v n) (v mu);
  E.mod_exp_mont_pow2_lemma (bits t) nLen (bn_v n) (v mu) (bn_v accM) c;
  assert (bn_v acc_pow2c < bn_v n);

  Math.Lemmas.lemma_mult_le_right nLen (v bits_c + 1) table_len;
  let a_powbits_c = sub t1 (v bits_c * nLen) nLen in
  bn_mod_exp_mont_precomp_table_lemma n mu table_len aM oneM;
  E.mod_exp_mont_precomp_table_lemma (bits t) nLen (bn_v n) (v mu) table_len (bn_v aM) (v bits_c);
  assert (bn_v a_powbits_c < bn_v n);

  let res = BM.bn_mont_mul n mu acc_pow2c a_powbits_c in
  BM.bn_mont_mul_lemma n mu acc_pow2c a_powbits_c


val bn_mod_exp_fw_precomp_table:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> l:size_pos{l <= bits t /\ pow2 l * nLen <= max_size_t}
  -> r2:lbignum t nLen ->
  lbignum t nLen

let bn_mod_exp_fw_precomp_table #t #nLen n mu aM bBits b l r2 =
  let bLen = blocks bBits (bits t) in
  let one = BN.bn_from_uint nLen (uint #t 1) in
  let oneM = BM.bn_to_mont n mu r2 one in

  let table_len = pow2 l in
  Math.Lemmas.pow2_le_compat l 1;
  let table = bn_mod_exp_mont_precomp_table n mu table_len aM oneM in
  let accM  = Loops.repeati (bBits / l) (bn_mod_exp_mont_precomp_f #t #nLen n mu bBits bLen b l table_len table) oneM in
  let res = bn_mod_exp_mont_precomp_rem #t #nLen n mu bBits bLen b l table_len table accM in
  res


let bn_mod_exp_fw_precompr2 #t nLen n a bBits b l r2 =
  let mu = BI.mod_inv_limb n.[0] in
  let aM = BM.bn_to_mont n mu r2 a in
  let resM = bn_mod_exp_fw_precomp_table #t #nLen n mu aM bBits b l r2 in
  BM.bn_from_mont n mu resM


let bn_mod_exp_fw_precompr2_lemma #t nLen n a bBits b l r2 = admit()


let bn_mod_exp_fw #t nLen nBits n a bBits b l =
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  bn_mod_exp_fw_precompr2 #t nLen n a bBits b l r2

let bn_mod_exp_fw_lemma #t nLen nBits n a bBits b l =
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  BM.bn_precomp_r2_mod_n_lemma nBits n;
  bn_mod_exp_fw_precompr2_lemma #t nLen n a bBits b l r2
