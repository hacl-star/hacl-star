module Hacl.Spec.Bignum.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Montgomery
open Hacl.Spec.Bignum.ModInvLimb

module BL = Hacl.Spec.Exponentiation.Lemmas
module M = Hacl.Spec.Montgomery.Lemmas


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_check_mod_exp #t #nLen n a bBits b =
  let pbits = bits t in
  let m0 = bn_check_modulus n in
  let m1 = bn_is_zero_mask b in
  bn_is_zero_mask_lemma b;
  assert (if v m1 = 0 then bn_v b > 0 else bn_v b = 0);
  assert (v m1 = 0 \/ v m1 = ones_v t);
  let m1' = lognot m1 in
  lognot_lemma m1;
  assert (if v m1' = 0 then bn_v b = 0 else bn_v b > 0);

  bn_eval_bound b (blocks bBits pbits);
  let m2 =
    if bBits < pbits * blocks bBits pbits then begin
      bn_lt_pow2_mask_lemma b bBits;
      bn_lt_pow2_mask b bBits end
    else begin
      Math.Lemmas.pow2_le_compat bBits (pbits * blocks bBits pbits);
      ones t SEC end in
  assert (if v m2 = 0 then pow2 bBits <= bn_v b else bn_v b < pow2 bBits);

  let m3 = bn_lt_mask a n in
  bn_lt_mask_lemma a n;
  assert (if v m3 = 0 then bn_v a >= bn_v n else bn_v a < bn_v n);

  let m = m1' &. m2 &. m3 in
  logand_ones (m1' &. m2);
  logand_zeros (m1' &. m2);
  logand_ones m1';
  logand_zeros m1';
  let r = m0 &. m in
  logand_lemma m0 m;
  r


val bn_mod_exp_f:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> i:nat{i < bBits}
  -> aM_accM: tuple2 (lbignum t nLen) (lbignum t nLen) ->
  tuple2 (lbignum t nLen) (lbignum t nLen)

let bn_mod_exp_f #t #nLen n mu bBits bLen b i (aM, accM) =
  let is_bit_set = not (Hacl.Spec.Bignum.Base.unsafe_bool_of_limb0 (bn_get_ith_bit b i)) in
  let accM = if is_bit_set then bn_mont_mul n mu aM accM else accM in // acc = (acc * a) % n
  let aM = bn_mont_sqr n mu aM in // a = (a * a) % n
  (aM, accM)


val bn_mod_exp_mont:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> acc:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> r2:lbignum t nLen ->
  lbignum t nLen

let bn_mod_exp_mont #t nLen n a acc bBits b r2 =
  let bLen = blocks bBits (bits t) in
  let mu = mod_inv_limb n.[0] in

  let aM = bn_to_mont n mu r2 a in
  let accM = bn_to_mont n mu r2 acc in
  let (aM, accM) = repeati bBits (bn_mod_exp_f n mu bBits bLen b) (aM, accM) in
  bn_from_mont n mu accM


let bn_mod_exp_precompr2 #t nLen n a bBits b r2 =
  let acc = bn_from_uint nLen (uint #t 1) in
  bn_mod_exp_mont nLen n a acc bBits b r2


val bn_mod_exp_f_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> i:nat{i < bBits}
  -> aM_accM0: tuple2 (lbignum t nLen) (lbignum t nLen) -> Lemma
  (requires
   (let (aM0, accM0) = aM_accM0 in
    (1 + (bn_v n % pow2 (bits t)) * v mu) % pow2 (bits t) == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\
    bn_v aM0 < bn_v n /\ bn_v accM0 < bn_v n))
  (ensures
   (let (aM0, accM0) = aM_accM0 in
    let (aM1, accM1) = bn_mod_exp_f n mu bBits bLen b i aM_accM0 in
    let (aM2, accM2) = BL.mod_exp_mont_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) i (bn_v aM0, bn_v accM0) in
    bn_v aM1 == aM2 /\ bn_v accM1 == accM2 /\
    bn_v aM1 < bn_v n /\ bn_v accM1 < bn_v n))

let bn_mod_exp_f_lemma #t #nLen n mu bBits bLen b i (aM0, accM0) =
  let (aM1, accM1) = bn_mod_exp_f n mu bBits bLen b i (aM0, accM0) in
  let (aM2, accM2) = BL.mod_exp_mont_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) i (bn_v aM0, bn_v accM0) in
  bn_mont_sqr_lemma n mu aM0;
  assert (bn_v aM1 == aM2);
  bn_get_ith_bit_lemma b i;
  if (bn_v b / pow2 i % 2 = 1) then bn_mont_mul_lemma n mu aM0 accM0;
  assert (bn_v accM1 == accM2)


val bn_mod_exp_mont_loop_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> i:size_nat{i <= bBits}
  -> aM_accM0: tuple2 (lbignum t nLen) (lbignum t nLen) -> Lemma
  (requires
   (let (aM0, accM0) = aM_accM0 in
    (1 + (bn_v n % pow2 (bits t)) * v mu) % pow2 (bits t) == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\
    bn_v aM0 < bn_v n /\ bn_v accM0 < bn_v n))
  (ensures
   (let (aM0, accM0) = aM_accM0 in
    let (aM1, accM1) = repeati i (bn_mod_exp_f n mu bBits bLen b) (aM0, accM0) in
    let (aM2, accM2) = repeati i (BL.mod_exp_mont_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v aM0, bn_v accM0) in
    bn_v aM1 == aM2 /\ bn_v accM1 == accM2 /\
    bn_v aM1 < bn_v n /\ bn_v accM1 < bn_v n))

let rec bn_mod_exp_mont_loop_lemma #t #nLen n mu bBits bLen b i (aM0, accM0) =
  let (aM1, accM1) = repeati i (bn_mod_exp_f n mu bBits bLen b) (aM0, accM0) in
  let (aM2, accM2) = repeati i (BL.mod_exp_mont_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v aM0, bn_v accM0) in

  if i = 0 then begin
    eq_repeati0 i (bn_mod_exp_f n mu bBits bLen b) (aM0, accM0);
    eq_repeati0 i (BL.mod_exp_mont_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v aM0, bn_v accM0);
    () end
  else begin
    unfold_repeati i (bn_mod_exp_f n mu bBits bLen b) (aM0, accM0) (i - 1);
    unfold_repeati i (BL.mod_exp_mont_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v aM0, bn_v accM0) (i - 1);
    let (aM3, accM3) = repeati (i - 1) (bn_mod_exp_f n mu bBits bLen b) (aM0, accM0) in
    let (aM4, accM4) = repeati (i - 1) (BL.mod_exp_mont_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v aM0, bn_v accM0) in
    assert ((aM1, accM1) == bn_mod_exp_f n mu bBits bLen b (i - 1) (aM3, accM3));
    assert ((aM2, accM2) == BL.mod_exp_mont_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) (i - 1) (aM4, accM4));
    bn_mod_exp_mont_loop_lemma n mu bBits bLen b (i - 1) (aM0, accM0);
    assert (bn_v aM3 == aM4 /\ bn_v accM3 == accM4);
    bn_mod_exp_f_lemma n mu bBits bLen b (i - 1) (aM3, accM3);
    () end


val bn_mod_exp_mont_lemma_aux:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> r2:lbignum t nLen -> Lemma
  (requires
    bn_v n % 2 = 1 /\ 1 < bn_v n /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\ bn_v a < bn_v n /\
    bn_v r2 == pow2 (2 * bits t * nLen) % bn_v n)
  (ensures
   (let mu = mod_inv_limb n.[0] in
    let res1 = bn_mod_exp_precompr2 nLen n a bBits b r2 in
    let res2 = BL.mod_exp_mont_ll (bits t) nLen (bn_v n) (v mu) (bn_v a) bBits (bn_v b) in
    bn_v res1 == res2 /\ bn_v res1 < bn_v n))

let bn_mod_exp_mont_lemma_aux #t nLen n a bBits b r2 =
  let bLen = blocks bBits (bits t) in

  let acc = bn_from_uint nLen (uint #t 1) in
  bn_from_uint_lemma nLen (uint #t 1);
  assert (bn_v acc == 1);

  let mu = mod_inv_limb n.[0] in
  bn_eval_index n 0;
  assert (bn_v n % pow2 (bits t) == v n.[0]);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v n) 2 (bits t);
  assert (v n.[0] % 2 = 1); // since bn_v n % 2 = 1
  mod_inv_limb_lemma n.[0];

  let aM0 = bn_to_mont n mu r2 a in
  bn_to_mont_lemma n mu r2 a;

  let accM0 = bn_to_mont n mu r2 acc in
  bn_to_mont_lemma n mu r2 acc;

  let (aM1, accM1) = repeati bBits (bn_mod_exp_f n mu bBits bLen b) (aM0, accM0) in
  bn_mod_exp_mont_loop_lemma n mu bBits bLen b bBits (aM0, accM0);

  let res = bn_from_mont n mu accM1 in
  bn_from_mont_lemma n mu accM1


let bn_mod_exp_precompr2_lemma #t nLen n a bBits b r2 =
  let mu = mod_inv_limb n.[0] in
  let res1 = bn_mod_exp_precompr2 nLen n a bBits b r2 in
  let res2 = BL.mod_exp_mont_ll (bits t) nLen (bn_v n) (v mu) (bn_v a) bBits (bn_v b) in
  bn_mod_exp_mont_lemma_aux nLen n a bBits b r2;
  assert (bn_v res1 == res2 /\ bn_v res1 < bn_v n);

  bn_eval_index n 0;
  assert (bn_v n % pow2 (bits t) == v n.[0]);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v n) 2 (bits t);
  assert (v n.[0] % 2 = 1); // since bn_v n % 2 = 1
  mod_inv_limb_lemma n.[0];
  assert ((1 + (bn_v n % pow2 (bits t)) * v mu) % pow2 (bits t) == 0);

  bn_eval_bound n nLen;
  let d, k = M.eea_pow2_odd (bits t * nLen) (bn_v n) in
  M.mont_preconditions (bits t) nLen (bn_v n) (v mu);
  BL.mod_exp_mont_ll_lemma (bits t) nLen (bn_v n) d (v mu) (bn_v a) bBits (bn_v b)

///
///  Montgomery ladder for exponentiation
///

let bn_mod_exp_mont_ladder_t (t:limb_t) (nLen:size_pos) (bBits:size_pos) (i:nat{i <= bBits}) =
  tuple3 (lbignum t nLen) (lbignum t nLen) (limb t)

val bn_mod_exp_mont_ladder_f:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> i:nat{i < bBits}
  -> rM0_rM1_privbit: tuple3 (lbignum t nLen) (lbignum t nLen) (limb t) ->
  tuple3 (lbignum t nLen) (lbignum t nLen) (limb t)

let bn_mod_exp_mont_ladder_f #t #nLen n mu bBits bLen b i (rM0, rM1, privbit) =
  let bit = bn_get_ith_bit b (bBits - i - 1) in
  let sw = bit ^. privbit in
  let rM0, rM1 = cswap2 sw rM0 rM1 in
  let rM0' = bn_mont_sqr n mu rM0 in // rM0 * rM0 % n
  let rM1' = bn_mont_mul n mu rM1 rM0 in // rM1 * rM0 % n
  (rM0', rM1', bit)


val bn_mod_exp_mont_ladder_:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> acc:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> r2:lbignum t nLen ->
  lbignum t nLen

let bn_mod_exp_mont_ladder_ #t nLen n a one bBits b r2 =
  let bLen = blocks bBits (bits t) in
  let mu = mod_inv_limb n.[0] in

  let rM0 = bn_to_mont n mu r2 one in
  let rM1 = bn_to_mont n mu r2 a in
  let sw = uint #t 0 in
  let (rM0', rM1', sw') = repeat_gen bBits (bn_mod_exp_mont_ladder_t t nLen bBits)
    (bn_mod_exp_mont_ladder_f n mu bBits bLen b) (rM0, rM1, sw) in
  let (rM0', rM1') = cswap2 sw' rM0' rM1' in
  bn_from_mont n mu rM0'


let bn_mod_exp_mont_ladder_precompr2 #t nLen n a bBits b r2 =
  let acc = bn_from_uint nLen (uint #t 1) in
  bn_mod_exp_mont_ladder_ nLen n a acc bBits b r2


val lemma_bit_xor_is_sum_mod2: #t:limb_t -> a:limb t -> b:limb t -> Lemma
  (requires v a <= 1 /\ v b <= 1)
  (ensures  v (a ^. b) == (v a + v b) % 2)

let lemma_bit_xor_is_sum_mod2 #t a b =
  match t with
  | U32 ->
    logxor_spec a b;
    assert_norm (UInt32.logxor 0ul 0ul == 0ul);
    assert_norm (UInt32.logxor 0ul 1ul == 1ul);
    assert_norm (UInt32.logxor 1ul 0ul == 1ul);
    assert_norm (UInt32.logxor 1ul 1ul == 0ul)
  | U64 ->
    logxor_spec a b;
    assert_norm (UInt64.logxor 0uL 0uL == 0uL);
    assert_norm (UInt64.logxor 0uL 1uL == 1uL);
    assert_norm (UInt64.logxor 1uL 0uL == 1uL);
    assert_norm (UInt64.logxor 1uL 1uL == 0uL)


val bn_mod_exp_mont_ladder_f_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> i:nat{i < bBits}
  -> rM0_rM1_sw: tuple3 (lbignum t nLen) (lbignum t nLen) (limb t) -> Lemma
  (requires
   (let (rM0, rM1, sw) = rM0_rM1_sw in
    (1 + (bn_v n % pow2 (bits t)) * v mu) % pow2 (bits t) == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\
    bn_v rM0 < bn_v n /\ bn_v rM1 < bn_v n /\ v sw <= 1))
  (ensures
   (let (rM0, rM1, sw) = rM0_rM1_sw in
    let (rM0', rM1', sw') = bn_mod_exp_mont_ladder_f n mu bBits bLen b i (rM0, rM1, sw) in
    let (rM0'', rM1'', sw'') = BL.mod_exp_mont_ladder_swap_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) i (bn_v rM0, bn_v rM1, v sw) in
    bn_v rM0' == rM0'' /\ bn_v rM1' == rM1'' /\ v sw' == sw'' /\
    bn_v rM0' < bn_v n /\ bn_v rM1' < bn_v n /\ v sw' <= 1))

let bn_mod_exp_mont_ladder_f_lemma #t #nLen n mu bBits bLen b i (rM0, rM1, sw) =
  let (rM0', rM1', sw') = bn_mod_exp_mont_ladder_f n mu bBits bLen b i (rM0, rM1, sw) in
  let (rM0'', rM1'', sw'') = BL.mod_exp_mont_ladder_swap_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) i (bn_v rM0, bn_v rM1, v sw) in
  let bit = bn_get_ith_bit b (bBits - i - 1) in
  bn_get_ith_bit_lemma b (bBits - i - 1);
  //assert (v bit == bn_v b / pow2 (bBits - i - 1) % 2);
  let sw1 = bit ^. sw in
  lemma_bit_xor_is_sum_mod2 bit sw;
  let rM2, rM3 = cswap2 sw1 rM0 rM1 in
  cswap2_lemma sw1 rM0 rM1;
  let rM2' = bn_mont_sqr n mu rM2 in
  bn_mont_sqr_lemma n mu rM2;
  let rM3' = bn_mont_mul n mu rM3 rM2 in
  bn_mont_mul_lemma n mu rM3 rM2;
  assert (rM0' == rM2' /\ rM1' == rM3' /\ sw' == bit);
  assert (bn_v rM0' == rM0'' /\ bn_v rM1' == rM1'' /\ v sw' == sw'')


val bn_mod_exp_mont_ladder_loop_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> bBits:size_pos
  -> bLen:size_nat{bLen == blocks bBits (bits t)}
  -> b:lbignum t bLen
  -> i:size_nat{i <= bBits}
  -> rM0_rM1_sw: tuple3 (lbignum t nLen) (lbignum t nLen) (limb t) -> Lemma
  (requires
   (let (rM0, rM1, sw) = rM0_rM1_sw in
    (1 + (bn_v n % pow2 (bits t)) * v mu) % pow2 (bits t) == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\
    bn_v rM0 < bn_v n /\ bn_v rM1 < bn_v n /\ v sw <= 1))
  (ensures
   (let (rM0, rM1, sw) = rM0_rM1_sw in
    let (rM0', rM1', sw') = repeat_gen i (bn_mod_exp_mont_ladder_t t nLen bBits)
      (bn_mod_exp_mont_ladder_f n mu bBits bLen b) (rM0, rM1, sw) in
    let (rM0'', rM1'', sw'') = repeati i
      (BL.mod_exp_mont_ladder_swap_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v rM0, bn_v rM1, v sw) in
    bn_v rM0' == rM0'' /\ bn_v rM1' == rM1'' /\ v sw' == sw'' /\
    bn_v rM0' < bn_v n /\ bn_v rM1' < bn_v n /\ v sw' <= 1))

let rec bn_mod_exp_mont_ladder_loop_lemma #t #nLen n mu bBits bLen b i (rM0, rM1, sw) =
  let (rM0', rM1', sw') = repeat_gen i (bn_mod_exp_mont_ladder_t t nLen bBits)
      (bn_mod_exp_mont_ladder_f n mu bBits bLen b) (rM0, rM1, sw) in
  let (rM0'', rM1'', sw'') = repeati i
    (BL.mod_exp_mont_ladder_swap_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v rM0, bn_v rM1, v sw) in

  if i = 0 then begin
    eq_repeat_gen0 i (bn_mod_exp_mont_ladder_t t nLen bBits) (bn_mod_exp_mont_ladder_f n mu bBits bLen b) (rM0, rM1, sw);
    eq_repeati0 i (BL.mod_exp_mont_ladder_swap_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v rM0, bn_v rM1, v sw);
    () end
  else begin
    unfold_repeat_gen i (bn_mod_exp_mont_ladder_t t nLen bBits) (bn_mod_exp_mont_ladder_f n mu bBits bLen b) (rM0, rM1, sw) (i - 1);
    unfold_repeati i (BL.mod_exp_mont_ladder_swap_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v rM0, bn_v rM1, v sw) (i - 1);

    let (rM2', rM3', sw1') = repeat_gen (i - 1) (bn_mod_exp_mont_ladder_t t nLen bBits)
      (bn_mod_exp_mont_ladder_f n mu bBits bLen b) (rM0, rM1, sw) in
    let (rM2'', rM3'', sw1'') = repeati (i - 1) (BL.mod_exp_mont_ladder_swap_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b)) (bn_v rM0, bn_v rM1, v sw) in
    assert ((rM0', rM1', sw') == bn_mod_exp_mont_ladder_f n mu bBits bLen b (i - 1) (rM2', rM3', sw1'));
    assert ((rM0'', rM1'', sw'') == BL.mod_exp_mont_ladder_swap_f_ll (bits t) nLen (bn_v n) (v mu) bBits (bn_v b) (i - 1) (rM2'', rM3'', sw1''));
    bn_mod_exp_mont_ladder_loop_lemma n mu bBits bLen b (i - 1) (rM0, rM1, sw);
    assert (bn_v rM2' == rM2'' /\ bn_v rM3' == rM3'' /\ v sw1' == sw1'');
    bn_mod_exp_mont_ladder_f_lemma n mu bBits bLen b (i - 1) (rM2', rM3', sw1');
    () end


val bn_mod_exp_mont_ladder_lemma_aux:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> r2:lbignum t nLen -> Lemma
  (requires
    bn_v n % 2 = 1 /\ 1 < bn_v n /\
    0 < bn_v b /\ bn_v b < pow2 bBits /\ bn_v a < bn_v n /\
    bn_v r2 == pow2 (2 * bits t * nLen) % bn_v n)
  (ensures
   (let mu = mod_inv_limb n.[0] in
    let res1 = bn_mod_exp_mont_ladder_precompr2 nLen n a bBits b r2 in
    let res2 = BL.mod_exp_mont_ladder_swap_ll (bits t) nLen (bn_v n) (v mu) (bn_v a) bBits (bn_v b) in
    bn_v res1 == res2 /\ bn_v res1 < bn_v n))

let bn_mod_exp_mont_ladder_lemma_aux #t nLen n a bBits b r2 =
  let bLen = blocks bBits (bits t) in

  let one = bn_from_uint nLen (uint #t 1) in
  bn_from_uint_lemma nLen (uint #t 1);
  assert (bn_v one == 1);

  let mu = mod_inv_limb n.[0] in
  bn_eval_index n 0;
  assert (bn_v n % pow2 (bits t) == v n.[0]);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v n) 2 (bits t);
  assert (v n.[0] % 2 = 1); // since bn_v n % 2 = 1
  mod_inv_limb_lemma n.[0];

  let rM0 = bn_to_mont n mu r2 one in
  bn_to_mont_lemma n mu r2 one;

  let rM1 = bn_to_mont n mu r2 a in
  bn_to_mont_lemma n mu r2 a;

  let sw = uint #t 0 in
  let (rM0', rM1', sw') = repeat_gen bBits (bn_mod_exp_mont_ladder_t t nLen bBits)
    (bn_mod_exp_mont_ladder_f n mu bBits bLen b) (rM0, rM1, sw) in
  bn_mod_exp_mont_ladder_loop_lemma n mu bBits bLen b bBits (rM0, rM1, sw);

  let (rM0'', rM1'') = cswap2 sw' rM0' rM1' in
  cswap2_lemma sw' rM0' rM1';
  let res = bn_from_mont n mu rM0'' in
  bn_from_mont_lemma n mu rM0''


let bn_mod_exp_mont_ladder_precompr2_lemma #t nLen n a bBits b r2 =
  let mu = mod_inv_limb n.[0] in
  let res1 = bn_mod_exp_mont_ladder_precompr2 nLen n a bBits b r2 in
  let res2 = BL.mod_exp_mont_ladder_swap_ll (bits t) nLen (bn_v n) (v mu) (bn_v a) bBits (bn_v b) in
  bn_mod_exp_mont_ladder_lemma_aux nLen n a bBits b r2;
  assert (bn_v res1 == res2 /\ bn_v res1 < bn_v n);

  bn_eval_index n 0;
  assert (bn_v n % pow2 (bits t) == v n.[0]);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v n) 2 (bits t);
  assert (v n.[0] % 2 = 1); // since bn_v n % 2 = 1
  mod_inv_limb_lemma n.[0];
  assert ((1 + (bn_v n % pow2 (bits t)) * v mu) % pow2 (bits t) == 0);

  bn_eval_bound n nLen;
  let d, k = M.eea_pow2_odd (bits t * nLen) (bn_v n) in
  M.mont_preconditions (bits t) nLen (bn_v n) (v mu);
  BL.mod_exp_mont_ladder_swap_ll_lemma (bits t) nLen (bn_v n) d (v mu) (bn_v a) bBits (bn_v b)


let bn_mod_exp #t nLen nBits n a bBits b =
  let r2 = bn_precomp_r2_mod_n nBits n in
  bn_mod_exp_precompr2 nLen n a bBits b r2


let bn_mod_exp_lemma #t nLen nBits n a bBits b =
  let r2 = bn_precomp_r2_mod_n nBits n in
  bn_precomp_r2_mod_n_lemma nBits n;
  bn_mod_exp_precompr2_lemma nLen n a bBits b r2


let bn_mod_exp_mont_ladder #t nLen nBits n a bBits b =
  let r2 = bn_precomp_r2_mod_n nBits n in
  bn_mod_exp_mont_ladder_precompr2 nLen n a bBits b r2


let bn_mod_exp_mont_ladder_lemma #t nLen nBits n a bBits b =
  let r2 = bn_precomp_r2_mod_n nBits n in
  bn_precomp_r2_mod_n_lemma nBits n;
  bn_mod_exp_mont_ladder_precompr2_lemma nLen n a bBits b r2
