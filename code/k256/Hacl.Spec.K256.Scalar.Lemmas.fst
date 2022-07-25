module Hacl.Spec.K256.Scalar.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Hacl.Spec.K256.Scalar

module S = Spec.K256
module SD = Hacl.Spec.Bignum.Definitions
module SB = Hacl.Spec.Bignum
module BB = Hacl.Spec.Bignum.Base


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val qas_nat4_is_qas_nat (f:qelem_lseq) :
  Lemma (SD.bn_v f == qas_nat4 (f.[0], f.[1], f.[2], f.[3]))
let qas_nat4_is_qas_nat f =
  SD.bn_eval_unfold_i f 4;
  SD.bn_eval_unfold_i f 3;
  SD.bn_eval_unfold_i f 2;
  SD.bn_eval_unfold_i f 1;
  SD.bn_eval0 f


val qas_nat4_inj (f1 f2:qelem4) : Lemma
  (requires qas_nat4 f1 = qas_nat4 f2)
  (ensures
   (let (a0,a1,a2,a3) = f1 in
    let (b0,b1,b2,b3) = f2 in
    a0 == b0 /\ a1 == b1 /\ a2 == b2 /\ a3 == b3))

let qas_nat4_inj f1 f2 =
  let (a0,a1,a2,a3) = f1 in
  let (b0,b1,b2,b3) = f2 in
  let bf1 = create4 a0 a1 a2 a3 in
  let bf2 = create4 b0 b1 b2 b3 in
  qas_nat4_is_qas_nat bf1;
  qas_nat4_is_qas_nat bf2;
  SD.bn_eval_inj 4 bf1 bf2


#push-options "--ifuel 1"
val is_qelem_zero_vartime4_lemma: f:qelem4 ->
  Lemma (is_qelem_zero_vartime4 f == (qas_nat4 f = 0))
let is_qelem_zero_vartime4_lemma f = ()

val is_qelem_lt_q_vartime4_lemma: f:qelem4 ->
  Lemma (is_qelem_lt_q_vartime4 f == (qas_nat4 f < S.q))
let is_qelem_lt_q_vartime4_lemma f =
  assert_norm (0xbfd25e8cd0364141 + 0xbaaedce6af48a03b * pow2 64 +
    0xfffffffffffffffe * pow2 128 + 0xffffffffffffffff * pow2 192 = S.q)

val is_qelem_le_q_halved_vartime4_lemma: f:qelem4 ->
  Lemma (is_qelem_le_q_halved_vartime4 f == (qas_nat4 f <= S.q / 2))
let is_qelem_le_q_halved_vartime4_lemma f =
  assert_norm (0xdfe92f46681b20a0 + 0x5d576e7357a4501d * pow2 64 +
    0xffffffffffffffff * pow2 128 + 0x7fffffffffffffff * pow2 192 = S.q / 2)

val is_qelem_eq_vartime4_lemma: f1:qelem4 -> f2:qelem4 ->
  Lemma (is_qelem_eq_vartime4 f1 f2 == (qas_nat4 f1 = qas_nat4 f2))
let is_qelem_eq_vartime4_lemma f1 f2 =
  if qas_nat4 f1 = qas_nat4 f2 then qas_nat4_inj f1 f2
#pop-options


val lemma_check_overflow: b:nat{b < pow2 256} ->
  Lemma (let overflow = (b + (pow2 256 - S.q)) / pow2 256 in
    overflow = (if b < S.q then 0 else 1))

let lemma_check_overflow b =
  let overflow = (b + (pow2 256 - S.q)) / pow2 256 in
  if b < S.q then begin
    assert (pow2 256 + b - S.q < pow2 256);
    assert (pow2 256 - S.q <= pow2 256 + b - S.q);
    assert_norm (0 < pow2 256 - S.q);
    Math.Lemmas.small_div (pow2 256 + b - S.q) (pow2 256);
    assert (overflow = 0) end
  else begin
    assert (pow2 256 <= pow2 256 + b - S.q);
    Math.Lemmas.lemma_div_le (pow2 256) (pow2 256 + b - S.q) (pow2 256);
    Math.Lemmas.cancel_mul_div 1 (pow2 256);
    assert (1 <= overflow);

    assert (pow2 256 + b - S.q < pow2 256 + pow2 256 - S.q);
    assert (pow2 256 + b - S.q <= pow2 256 + pow2 256 - S.q - 1);
    Math.Lemmas.lemma_div_le (pow2 256 + b - S.q) (pow2 256 + pow2 256 - S.q - 1) (pow2 256);
    assert_norm ((pow2 256 + pow2 256 - S.q - 1) / pow2 256 = 1);
    assert (overflow <= 1) end


val lemma_get_carry_from_bn_add: r:nat{r < pow2 256} -> c:nat ->
  Lemma ((r + c * pow2 256) / pow2 256 = c)

let lemma_get_carry_from_bn_add r c =
  Math.Lemmas.lemma_div_plus r c (pow2 256);
  Math.Lemmas.small_div r (pow2 256)


val mod_short_lseq_lemma_aux: a:qelem_lseq -> out:qelem_lseq -> c:BB.carry U64 -> Lemma
  (requires v c * pow2 256 + SD.bn_v out = SD.bn_v a + pow2 256 - S.q)
  (ensures  SD.bn_v (map2 (BB.mask_select (u64 0 -. c)) out a) == SD.bn_v a % S.q)

let mod_short_lseq_lemma_aux a out c =
  assert_norm (pow2 256 - S.q < S.q);

  let mask = u64 0 -. c in
  let out1 = map2 (BB.mask_select mask) out a in
  assert (v mask = (if v c = 0 then 0 else ones_v U64));
  BB.lseq_mask_select_lemma out a mask;
  assert (out1 == (if v c = 0 then a else out));

  SD.bn_eval_bound a 4;
  SD.bn_eval_bound out 4;
  lemma_check_overflow (SD.bn_v a);
  lemma_get_carry_from_bn_add (SD.bn_v out) (v c);
  assert (v c = (if SD.bn_v a < S.q then 0 else 1));

  if SD.bn_v a < S.q then begin
    assert (SD.bn_v out1 == SD.bn_v a);
    Math.Lemmas.small_mod (SD.bn_v a) S.q end
  else begin
    assert (SD.bn_v out1 == SD.bn_v a + (pow2 256 - S.q) - pow2 256);
    Math.Lemmas.lemma_mod_sub (SD.bn_v a) S.q 1;
    assert (SD.bn_v out1 % S.q == SD.bn_v a % S.q);
    Math.Lemmas.small_mod (SD.bn_v out1) S.q end


val mod_short_lseq_lemma: a:qelem_lseq ->
  Lemma (SD.bn_v (mod_short_lseq a) == SD.bn_v a % S.q)

let mod_short_lseq_lemma a =
  let (t0,t1,t2,t3) = make_pow2_256_minus_order_k256 () in
  let tmp = create4 t0 t1 t2 t3 in
  let c, out = SB.bn_add a tmp in
  SB.bn_add_lemma a tmp;
  assert (v c * pow2 256 + SD.bn_v out = SD.bn_v a + SD.bn_v tmp);
  qas_nat4_is_qas_nat tmp;
  assert (SD.bn_v tmp == pow2 256 - S.q);

  mod_short_lseq_lemma_aux a out c


val mul_pow2_256_minus_q_lemma: len:size_nat -> resLen:size_nat{2 + len <= resLen} -> a:lseq uint64 len ->
  Lemma (let c, res = mul_pow2_256_minus_q_lseq len resLen a in
    v c * pow2 (64 * resLen) + SD.bn_v res = SD.bn_v a * (pow2 256 - S.q))

let mul_pow2_256_minus_q_lemma len resLen a =
  let t0 = u64 0x402da1732fc9bebf in
  let t1 = u64 0x4551231950b75fc4 in
  assert_norm (v t0 + v t1 * pow2 64 = pow2 256 - S.q - pow2 128);

  let t01 = create2 t0 t1 in
  SD.bn_eval_unfold_i t01 2;
  SD.bn_eval_unfold_i t01 1;
  SD.bn_eval0 t01;
  assert (SD.bn_v t01 = pow2 256 - S.q - pow2 128);

  let m0 = SB.bn_mul a t01 in // a * t01
  SB.bn_mul_lemma a t01;
  assert (SD.bn_v m0 == SD.bn_v a * SD.bn_v t01);

  let m10 = create resLen (u64 0) in
  let m1 = update_sub m10 2 len a in // a * t2 * pow2 128
  SD.bn_update_sub_eval m10 a 2;
  assert (SD.bn_v m1 = SD.bn_v m10 - SD.bn_v (sub m10 2 len) * pow2 128 + SD.bn_v a * pow2 128);
  SD.bn_eval_zeroes #U64 resLen resLen;
  eq_intro (sub m10 2 len) (create len (u64 0));
  SD.bn_eval_zeroes #U64 len len;
  assert (SD.bn_v m1 = SD.bn_v a * pow2 128);

  let c, m2 = SB.bn_add m1 m0 in // a * SECP256K1_N_C
  SB.bn_add_lemma m1 m0;
  assert (v c * pow2 (64 * resLen) + SD.bn_v m2 = SD.bn_v m1 + SD.bn_v m0);
  assert (v c * pow2 (64 * resLen) + SD.bn_v m2 = SD.bn_v a * pow2 128 + SD.bn_v a * SD.bn_v t01);
  Math.Lemmas.distributivity_add_right (SD.bn_v a) (pow2 128) (SD.bn_v t01);
  assert (v c * pow2 (64 * resLen) + SD.bn_v m2 = SD.bn_v a * (pow2 256 - S.q))


val mul_pow2_256_minus_q_lt_lemma: p:nat -> a:nat{a < pow2 p} ->
  Lemma (a * (pow2 256 - S.q) < pow2 (p + 129))

let mul_pow2_256_minus_q_lt_lemma p a =
  Math.Lemmas.lemma_mult_lt_right (pow2 256 - S.q) a (pow2 p);
  assert_norm (pow2 256 - S.q < pow2 129);
  Math.Lemmas.lemma_mult_lt_left (pow2 p) (pow2 256 - S.q) (pow2 129);
  Math.Lemmas.pow2_plus p 129


val carry_is_zero (c d e a:nat) : Lemma
  (requires
    a < pow2 d /\ e < pow2 d /\
    c * pow2 d + e = a)
  (ensures c = 0)

let carry_is_zero c d e a = ()


val mul_pow2_256_minus_q_add_lemma:
    len:size_nat -> resLen:size_nat{2 + len <= resLen /\ 4 <= resLen} -> d:nat
  -> a:lseq uint64 len -> e:lseq uint64 4 -> Lemma
  (requires SD.bn_v a < pow2 d /\ d + 129 < 64 * resLen)
  (ensures (let c, res = mul_pow2_256_minus_q_lseq_add len resLen a e in
    v c * pow2 (64 * resLen) + SD.bn_v res = SD.bn_v a * (pow2 256 - S.q) + SD.bn_v e /\
    SD.bn_v a * (pow2 256 - S.q) + SD.bn_v e < pow2 (d + 129) + pow2 256))

let mul_pow2_256_minus_q_add_lemma len resLen d a e =
  let c0, m = mul_pow2_256_minus_q_lseq len resLen a in // a * SECP256K1_N_C
  mul_pow2_256_minus_q_lemma len resLen a;
  assert (v c0 * pow2 (64 * resLen) + SD.bn_v m = SD.bn_v a * (pow2 256 - S.q));
  mul_pow2_256_minus_q_lt_lemma d (SD.bn_v a);
  assert (SD.bn_v a * (pow2 256 - S.q) < pow2 (d + 129));
  Math.Lemmas.pow2_lt_compat (64 * resLen) (d + 129);
  assert (SD.bn_v a * (pow2 256 - S.q) < pow2 (64 * resLen));

  SD.bn_eval_bound m resLen;
  assert (SD.bn_v m < pow2 (64 * resLen));
  carry_is_zero (v c0) (64 * resLen) (SD.bn_v m) (SD.bn_v a * (pow2 256 - S.q));
  assert (v c0 = 0 /\ SD.bn_v m = SD.bn_v a * (pow2 256 - S.q));

  let c1, res = SB.bn_add m e in // e + a * SECP256K1_N_C
  SB.bn_add_lemma m e;
  assert (v c1 * pow2 (64 * resLen) + SD.bn_v res == SD.bn_v a * (pow2 256 - S.q) + SD.bn_v e);
  SD.bn_eval_bound e 4;
  assert (SD.bn_v a * (pow2 256 - S.q) + SD.bn_v e < pow2 (d + 129) + pow2 256)


val mul_pow2_256_minus_q_add_lemma_carry_is_zero:
    len:size_nat -> resLen:size_nat{2 + len <= resLen /\ 4 <= resLen} -> d:nat
  -> a:lseq uint64 len -> e:lseq uint64 4 -> f:nat -> Lemma
  (requires
    SD.bn_v a < pow2 d /\ d + 129 < 64 * resLen /\
    256 <= f /\ d + 129 <= f /\ f + 1 < 64 * resLen)
  (ensures (let c, res = mul_pow2_256_minus_q_lseq_add len resLen a e in
    v c * pow2 (64 * resLen) + SD.bn_v res = SD.bn_v a * (pow2 256 - S.q) + SD.bn_v e /\
    v c = 0 /\ SD.bn_v a * (pow2 256 - S.q) + SD.bn_v e < pow2 (d + 129) + pow2 256))

let mul_pow2_256_minus_q_add_lemma_carry_is_zero len resLen d a e f =
  let c0, m = mul_pow2_256_minus_q_lseq_add len resLen a e in
  mul_pow2_256_minus_q_add_lemma len resLen d a e;
  let rhs_m = SD.bn_v a * (pow2 256 - S.q) + SD.bn_v e in
  assert (v c0 * pow2 (64 * resLen) + SD.bn_v m = rhs_m);
  assert (rhs_m < pow2 (d + 129) + pow2 256);
  Math.Lemmas.pow2_le_compat f 256;
  Math.Lemmas.pow2_le_compat f (d + 129);
  Math.Lemmas.pow2_double_sum f;
  assert (rhs_m < pow2 (f + 1));
  Math.Lemmas.pow2_lt_compat (64 * resLen) (f + 1);
  carry_is_zero (v c0) (64 * resLen) (SD.bn_v m) rhs_m;
  assert (v c0 = 0 /\ SD.bn_v m = rhs_m)


val lemma_m_bound: m:lseq uint64 7 -> Lemma
  (requires SD.bn_v m < pow2 385 + pow2 256)
  (ensures  SD.bn_v (sub m 4 3) < pow2 130)

let lemma_m_bound m =
  Math.Lemmas.pow2_lt_compat 385 256;
  Math.Lemmas.pow2_double_sum 385;
  SD.bn_eval_split_i m 4;
  assert (SD.bn_v m - SD.bn_v (sub m 0 4) = pow2 256 * SD.bn_v (sub m 4 3));
  Math.Lemmas.cancel_mul_div (SD.bn_v (sub m 4 3)) (pow2 256);
  Math.Lemmas.lemma_div_lt (SD.bn_v m - SD.bn_v (sub m 0 4)) 386 256;
  assert (SD.bn_v (sub m 4 3) < pow2 130)


val lemma_p_bound: p:lseq uint64 5 -> Lemma
  (requires SD.bn_v p < pow2 259 + pow2 256)
  (ensures  SD.bn_v (sub p 4 1) < pow2 4)

let lemma_p_bound p =
  Math.Lemmas.pow2_lt_compat 259 256;
  Math.Lemmas.pow2_double_sum 259;
  SD.bn_eval_split_i p 4;
  assert (SD.bn_v p - SD.bn_v (sub p 0 4) = pow2 256 * SD.bn_v (sub p 4 1));
  Math.Lemmas.cancel_mul_div (SD.bn_v (sub p 4 1)) (pow2 256);
  Math.Lemmas.lemma_div_lt (SD.bn_v p - SD.bn_v (sub p 0 4)) 260 256;
  assert (SD.bn_v (sub p 4 1) < pow2 4)


val mod_lseq_before_final_lemma_aux: a:lseq uint64 8 -> Lemma
  (let c0, m = mul_pow2_256_minus_q_lseq_add 4 7 (sub a 4 4) (sub a 0 4) in // a[0..3] + a[4..7] * SECP256K1_N_C
   let c1, p = mul_pow2_256_minus_q_lseq_add 3 5 (sub m 4 3) (sub m 0 4) in // m[0..3] + m[4..6] * SECP256K1_N_C
   let c2, r = mul_pow2_256_minus_q_lseq_add 1 4 (sub p 4 1) (sub p 0 4) in // p[0..3] + p[4] * SECP256K1_N_C
   let rhs_a = SD.bn_v (sub a 4 4) * (pow2 256 - S.q) + SD.bn_v (sub a 0 4) in
   let rhs_m = SD.bn_v (sub m 4 3) * (pow2 256 - S.q) + SD.bn_v (sub m 0 4) in
   let rhs_p = SD.bn_v (sub p 4 1) * (pow2 256 - S.q) + SD.bn_v (sub p 0 4) in

   v c0 = 0 /\ SD.bn_v m = rhs_a /\
   v c1 = 0 /\ SD.bn_v p = rhs_m /\
   v c2 * pow2 256 + SD.bn_v r = rhs_p /\ rhs_p < pow2 133 + pow2 256)

let mod_lseq_before_final_lemma_aux a =
  let c0, m = mul_pow2_256_minus_q_lseq_add 4 7 (sub a 4 4) (sub a 0 4) in // a[0..3] + a[4..7] * SECP256K1_N_C
  let rhs_a = SD.bn_v (sub a 4 4) * (pow2 256 - S.q) + SD.bn_v (sub a 0 4) in
  SD.bn_eval_bound (sub a 4 4) 4;
  mul_pow2_256_minus_q_add_lemma_carry_is_zero 4 7 256 (sub a 4 4) (sub a 0 4) 385;
  assert (v c0 = 0 /\ SD.bn_v m = rhs_a /\ rhs_a < pow2 385 + pow2 256);

  let c1, p = mul_pow2_256_minus_q_lseq_add 3 5 (sub m 4 3) (sub m 0 4) in // m[0..3] + m[4..6] * SECP256K1_N_C
  let rhs_m = SD.bn_v (sub m 4 3) * (pow2 256 - S.q) + SD.bn_v (sub m 0 4) in
  lemma_m_bound m;
  mul_pow2_256_minus_q_add_lemma_carry_is_zero 3 5 130 (sub m 4 3) (sub m 0 4) 259;
  assert (v c1 = 0 /\ SD.bn_v p = rhs_m); ///\ rhs_m < pow2 259 + pow2 256);

  let c2, r = mul_pow2_256_minus_q_lseq_add 1 4 (sub p 4 1) (sub p 0 4) in // p[0..3] + p[4] * SECP256K1_N_C
  lemma_p_bound p;
  mul_pow2_256_minus_q_add_lemma 1 4 4 (sub p 4 1) (sub p 0 4);
  let rhs_p = SD.bn_v (sub p 4 1) * (pow2 256 - S.q) + SD.bn_v (sub p 0 4) in
  assert (v c2 * pow2 256 + SD.bn_v r = rhs_p);
  assert (rhs_p < pow2 133 + pow2 256)


val lemma_b_pow2_256_plus_a_modq (a b: nat) :
 Lemma ((b * pow2 256 + a) % S.q = (b * (pow2 256 - S.q) + a) % S.q)

let lemma_b_pow2_256_plus_a_modq a b =
  calc (==) {
    (b * (pow2 256 - S.q) + a) % S.q;
    (==) { Math.Lemmas.distributivity_sub_right b (pow2 256) S.q }
    (b * pow2 256 - b * S.q + a) % S.q;
    (==) { Math.Lemmas.lemma_mod_sub (b * pow2 256 + a) S.q b }
    (b * pow2 256 + a) % S.q;
  }


val lemma_b_pow2_256_plus_a_modq_lseq: len:size_nat{4 <= len} -> a:lseq uint64 len ->
  Lemma (SD.bn_v a % S.q == (SD.bn_v (sub a 4 (len - 4)) * (pow2 256 - S.q) + SD.bn_v (sub a 0 4)) % S.q)

let lemma_b_pow2_256_plus_a_modq_lseq len a =
  lemma_b_pow2_256_plus_a_modq (SD.bn_v (sub a 0 4)) (SD.bn_v (sub a 4 (len - 4)));
  SD.bn_eval_split_i a 4


val mod_lseq_before_final_lemma: a:lseq uint64 8 ->
  Lemma (let (c, res) = mod_lseq_before_final a in
    v c * pow2 256 + SD.bn_v res < pow2 133 + pow2 256 /\
    (v c * pow2 256 + SD.bn_v res) % S.q == SD.bn_v a % S.q)

let mod_lseq_before_final_lemma a =
  let c0, m = mul_pow2_256_minus_q_lseq_add 4 7 (sub a 4 4) (sub a 0 4) in // a[0..3] + a[4..7] * SECP256K1_N_C
  let c1, p = mul_pow2_256_minus_q_lseq_add 3 5 (sub m 4 3) (sub m 0 4) in // m[0..3] + m[4..6] * SECP256K1_N_C
  let c2, r = mul_pow2_256_minus_q_lseq_add 1 4 (sub p 4 1) (sub p 0 4) in // p[0..3] + p[4] * SECP256K1_N_C

  let rhs_a = SD.bn_v (sub a 4 4) * (pow2 256 - S.q) + SD.bn_v (sub a 0 4) in
  let rhs_m = SD.bn_v (sub m 4 3) * (pow2 256 - S.q) + SD.bn_v (sub m 0 4) in
  let rhs_p = SD.bn_v (sub p 4 1) * (pow2 256 - S.q) + SD.bn_v (sub p 0 4) in

  mod_lseq_before_final_lemma_aux a;
  assert (v c0 = 0 /\ SD.bn_v m = rhs_a);
  assert (v c1 = 0 /\ SD.bn_v p = rhs_m);
  assert (v c2 * pow2 256 + SD.bn_v r = rhs_p);
  assert (rhs_p < pow2 133 + pow2 256);

  calc (==) { //(v c2 * pow2 256 + SD.bn_v r) % S.q;
    rhs_p % S.q;
    (==) { lemma_b_pow2_256_plus_a_modq_lseq 5 p }
    SD.bn_v p % S.q;
    (==) { }
    rhs_m % S.q;
    (==) { lemma_b_pow2_256_plus_a_modq_lseq 7 m }
    SD.bn_v m % S.q;
    (==) { }
    rhs_a % S.q;
    (==) { lemma_b_pow2_256_plus_a_modq_lseq 8 a }
    SD.bn_v a % S.q;
    }


val mod_lseq_lemma: a:lseq uint64 8 -> Lemma (SD.bn_v (mod_lseq a) == SD.bn_v a % S.q)
let mod_lseq_lemma a =
  let c0, r = mod_lseq_before_final a in
  mod_lseq_before_final_lemma a;
  assert ((v c0 * pow2 256 + SD.bn_v r) % S.q == SD.bn_v a % S.q);
  assert (v c0 * pow2 256 + SD.bn_v r < pow2 256 + pow2 133);

  let (t0,t1,t2,t3) = make_pow2_256_minus_order_k256 () in
  let tmp = create4 t0 t1 t2 t3 in
  qas_nat4_is_qas_nat tmp;
  assert (SD.bn_v tmp = pow2 256 - S.q);

  let c1, out = SB.bn_add r tmp in
  SB.bn_add_lemma r tmp;
  assert (v c1 * pow2 256 + SD.bn_v out = SD.bn_v r + pow2 256 - S.q);

  Math.Lemmas.small_mod (v c0 + v c1) (pow2 64);
  assert (v (c0 +. c1) == v c0 + v c1);
  let mask = u64 0 -. (c0 +. c1) in
  //let mask = u64 0 -. c1 in
  let res = map2 (BB.mask_select mask) out r in

  SD.bn_eval_bound r 4;
  SD.bn_eval_bound out 4;
  lemma_check_overflow (SD.bn_v r);
  lemma_get_carry_from_bn_add (SD.bn_v out) (v c1);
  assert (v c1 = (if SD.bn_v r < S.q then 0 else 1));

  if v c0 = 0 then begin
    assert (SD.bn_v r % S.q == SD.bn_v a % S.q);
    assert (res == mod_short_lseq r);
    mod_short_lseq_lemma r;
    assert (SD.bn_v res == SD.bn_v a % S.q) end
  else begin // v c0 = 1 ==> v c1 = 0
    assert ((pow2 256 + SD.bn_v r) % S.q == SD.bn_v a % S.q);
    assert (v c1 * pow2 256 + SD.bn_v out = SD.bn_v r + pow2 256 - S.q);
    assert (SD.bn_v r < pow2 133);
    assert_norm (pow2 256 - S.q < pow2 129);
    Math.Lemmas.pow2_lt_compat 133 129;
    Math.Lemmas.pow2_double_sum 133;
    assert (SD.bn_v r + pow2 256 - S.q < pow2 134);
    Math.Lemmas.pow2_lt_compat 256 134;
    carry_is_zero (v c1) 256 (SD.bn_v out) (SD.bn_v r + pow2 256 - S.q);
    assert (v c1 = 0);

    assert_norm (pow2 134 < S.q);
    assert (SD.bn_v r + pow2 256 - S.q < S.q);
    BB.lseq_mask_select_lemma out r mask;
    assert (SD.bn_v res == SD.bn_v r + pow2 256 - S.q);
    Math.Lemmas.lemma_mod_sub (pow2 256 + SD.bn_v r) S.q 1;
    assert (SD.bn_v res % S.q == SD.bn_v a % S.q);
    Math.Lemmas.small_mod (SD.bn_v res) S.q end


val qmul_shift_383_mod_2_lemma : l:lseq uint64 8 ->
  Lemma (v l.[5] / pow2 63 = SD.bn_v l / pow2 383 % 2)
let qmul_shift_383_mod_2_lemma l =
  calc (==) {
    v l.[5] / pow2 63;
    (==) { SD.bn_eval_index l 5 }
    SD.bn_v l / pow2 320 % pow2 64 / pow2 63;
    (==) { Math.Lemmas.pow2_modulo_division_lemma_1 (SD.bn_v l) 320 384 }
    SD.bn_v l % pow2 384 / pow2 320 / pow2 63;
    (==) { Math.Lemmas.division_multiplication_lemma (SD.bn_v l % pow2 384) (pow2 320) (pow2 63) }
    SD.bn_v l % pow2 384 / (pow2 320 * pow2 63);
    (==) { Math.Lemmas.pow2_plus 320 63 }
    SD.bn_v l % pow2 384 / pow2 383;
    (==) { Math.Lemmas.pow2_modulo_division_lemma_1 (SD.bn_v l) 383 384 }
    SD.bn_v l / pow2 383 % pow2 1;
    (==) { assert_norm (pow2 1 = 2) }
    SD.bn_v l / pow2 383 % 2;
  }


val qmul_shift_384_lemma_eval_fits : l:lseq uint64 8 ->
  Lemma (let res_b = SB.bn_rshift l 6 in
    let res_b_padded = create 4 (u64 0) in
    let res_b_padded = update_sub res_b_padded 0 2 res_b in
    SD.bn_v res_b_padded < pow2 128 /\
    SD.bn_v res_b_padded = SD.bn_v l / pow2 384)

let qmul_shift_384_lemma_eval_fits l =
  let res_b = SB.bn_rshift l 6 in
  let res_b_padded = create 4 (u64 0) in
  let res_b_padded = update_sub res_b_padded 0 2 res_b in
  SD.bn_eval_update_sub 2 res_b 4;
  assert (SD.bn_v res_b = SD.bn_v res_b_padded);
  SB.bn_rshift_lemma l 6;

  SD.bn_eval_bound res_b 2;
  assert (SD.bn_v res_b_padded < pow2 128)


val qmul_shift_384_lemma (a b:qelem_lseq) :
  Lemma (let x = SD.bn_v a * SD.bn_v b / pow2 383 % 2 in
    SD.bn_v (qmul_shift_384 a b) = SD.bn_v a * SD.bn_v b / pow2 384 + x)

let qmul_shift_384_lemma a b =
  let l = SB.bn_mul a b in
  SB.bn_mul_lemma a b;
  assert (SD.bn_v l = SD.bn_v a * SD.bn_v b);

  let res_b = SB.bn_rshift l 6 in
  let res_b_padded = create 4 (u64 0) in
  let res_b_padded = update_sub res_b_padded 0 2 res_b in
  qmul_shift_384_lemma_eval_fits l;
  assert (SD.bn_v res_b_padded < pow2 128);
  assert (SD.bn_v res_b_padded = SD.bn_v l / pow2 384);

  let c, res1_b = SB.bn_add1 res_b_padded (u64 1) in
  SB.bn_add1_lemma res_b_padded (u64 1);
  assert (v c * pow2 256 + SD.bn_v res1_b = SD.bn_v res_b_padded + 1);
  SD.bn_eval_bound res1_b 4;
  Math.Lemmas.pow2_lt_compat 256 128;
  carry_is_zero (v c) 256 (SD.bn_v res1_b) (SD.bn_v res_b_padded + 1);
  assert (v c = 0 /\ SD.bn_v res1_b = SD.bn_v res_b_padded + 1);

  let flag = l.[5] >>. 63ul in
  assert (v flag = v l.[5] / pow2 63);
  qmul_shift_383_mod_2_lemma l;
  assert (v flag = SD.bn_v l / pow2 383 % 2);

  let mask = u64 0 -. flag in
  assert (v mask = (if v flag = 0 then 0 else ones_v U64));
  let res = map2 (BB.mask_select mask) res1_b res_b_padded in
  BB.lseq_mask_select_lemma res1_b res_b_padded mask;
  assert (res == (if v flag = 0 then res_b_padded else res1_b))
