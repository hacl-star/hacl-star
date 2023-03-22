module Hacl.Impl.P256.Verify

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Point
open Hacl.Impl.P256.Scalar
open Hacl.Impl.P256.PointMul

open Hacl.Hash.SHA2
open Spec.Hash.Definitions

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.P256
module SM = Hacl.Spec.P256.Montgomery
module PS = Hacl.Impl.P256.Sign
module QI = Hacl.Impl.P256.Qinv

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// TODO: use variable time cmp with scalar
inline_for_extraction noextract
val are_r_and_s_valid: r:felem -> s:felem -> Stack bool
  (requires fun h -> live h r /\ live h s)
  (ensures  fun h0 res h1 -> modifies0 h0 h1 /\
    res ==
      (0 < as_nat h0 r && as_nat h0 r < S.order &&
       0 < as_nat h0 s && as_nat h0 s < S.order))

let are_r_and_s_valid r s =
  let is_r_valid = bn_is_lt_order_and_gt_zero_mask4 r in
  let is_s_valid = bn_is_lt_order_and_gt_zero_mask4 s in
  Hacl.Bignum.Base.unsafe_bool_of_limb is_r_valid &&
  Hacl.Bignum.Base.unsafe_bool_of_limb is_s_valid


val lemma_cancel_mont: a:S.qelem -> b:S.qelem ->
  Lemma ((a * SM.qmont_R % S.order * b * SM.qmont_R_inv) % S.order = a * b % S.order)

let lemma_cancel_mont a b =
  calc (==) {
    (a * SM.qmont_R % S.order * b * SM.qmont_R_inv) % S.order;
    (==) { Math.Lemmas.paren_mul_right (a * SM.qmont_R % S.order) b SM.qmont_R_inv }
    (a * SM.qmont_R % S.order * (b * SM.qmont_R_inv)) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * SM.qmont_R) (b * SM.qmont_R_inv) S.order }
    (a * SM.qmont_R * (b * SM.qmont_R_inv)) % S.order;
    (==) { Math.Lemmas.paren_mul_right a SM.qmont_R (b * SM.qmont_R_inv);
           Math.Lemmas.swap_mul SM.qmont_R (b * SM.qmont_R_inv) }
    (a * (b * SM.qmont_R_inv * SM.qmont_R)) % S.order;
    (==) { Math.Lemmas.paren_mul_right b SM.qmont_R_inv SM.qmont_R }
    (a * (b * (SM.qmont_R_inv * SM.qmont_R))) % S.order;
    (==) { Math.Lemmas.paren_mul_right a b (SM.qmont_R_inv * SM.qmont_R) }
    (a * b * (SM.qmont_R_inv * SM.qmont_R)) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (a * b) (SM.qmont_R_inv * SM.qmont_R) S.order }
    (a * b * (SM.qmont_R_inv * SM.qmont_R % S.order)) % S.order;
    (==) { assert_norm (SM.qmont_R_inv * SM.qmont_R % S.order = 1) }
    (a * b) % S.order;
  }


val qmul_mont_lemma: s:S.qelem -> sinv:S.qelem -> b:S.qelem -> Lemma
  (requires SM.fromDomain_ sinv == S.qinv (SM.fromDomain_ s))
  (ensures  (sinv * SM.fromDomain_ b * SM.qmont_R_inv) % S.order == S.qinv s * b % S.order)

let qmul_mont_lemma s sinv b =
  let s_mont = SM.fromDomain_ s in
  let b_mont = SM.fromDomain_ b in
  calc (==) {
    (sinv * b_mont * SM.qmont_R_inv) % S.order;
    (==) { SM.lemmaFromDomainToDomain sinv }
    (S.qinv s_mont * SM.qmont_R % S.order * b_mont * SM.qmont_R_inv) % S.order;
    (==) { lemma_cancel_mont (S.qinv s_mont) b_mont }
    (S.qinv s_mont * b_mont) % S.order;
    (==) { PS.lemma_mont_qinv s }
    ((S.qinv s * SM.qmont_R % S.order) * (b * SM.qmont_R_inv % S.order)) % S.order;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r
      (S.qinv s * SM.qmont_R % S.order) (b * SM.qmont_R_inv) S.order }
    ((S.qinv s * SM.qmont_R % S.order) * (b * SM.qmont_R_inv)) % S.order;
    (==) { Math.Lemmas.paren_mul_right (S.qinv s * SM.qmont_R % S.order) b SM.qmont_R_inv }
    ((S.qinv s * SM.qmont_R % S.order) * b * SM.qmont_R_inv) % S.order;
    (==) { lemma_cancel_mont (S.qinv s) b }
    S.qinv s * b % S.order;
  }


val qmul_mont: sinv:felem -> b:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h sinv /\ live h b /\ live h res /\
    disjoint sinv res /\ disjoint b res /\
    as_nat h sinv < S.order /\ as_nat h b < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.order /\
    as_nat h1 res = (as_nat h0 sinv * SM.fromDomain_ (as_nat h0 b) * SM.qmont_R_inv) % S.order)

[@CInline]
let qmul_mont sinv b res =
  let h0 = ST.get () in
  push_frame ();
  let tmp = create_felem () in
  from_qmont b tmp;
  let h1 = ST.get () in
  assert (as_nat h1 tmp == SM.fromDomain_ (as_nat h0 b));
  qmul sinv tmp res;
  let h2 = ST.get () in
  assert (as_nat h2 res = (as_nat h1 sinv * as_nat h1 tmp * SM.qmont_R_inv) % S.order);
  pop_frame ()


inline_for_extraction noextract
val ecdsa_verification_get_u12: u1:felem -> u2:felem -> r:felem -> s:felem -> z:felem -> Stack unit
  (requires fun h ->
    live h r /\ live h s /\ live h z /\ live h u1 /\ live h u2 /\
    disjoint u1 u2 /\ disjoint u1 z /\ disjoint u1 r /\ disjoint u1 s /\
    disjoint u2 z /\ disjoint u2 r /\ disjoint u2 s /\
    as_nat h s < S.order /\ as_nat h z < S.order /\ as_nat h r < S.order)
  (ensures fun h0 _ h1 -> modifies (loc u1 |+| loc u2) h0 h1 /\
    (let sinv = S.qinv (as_nat h0 s) in
    as_nat h1 u1 == sinv * as_nat h0 z % S.order /\
    as_nat h1 u2 == sinv * as_nat h0 r % S.order))

let ecdsa_verification_get_u12 u1 u2 r s z =
  push_frame ();
  let h0 = ST.get () in
  let sinv = create_felem () in
  QI.qinv sinv s;
  let h1 = ST.get () in
  assert (qmont_as_nat h1 sinv == S.qinv (qmont_as_nat h0 s));
  //assert (as_nat h2 sinv * SM.qmont_R_inv % S.order ==
    //S.qinv (as_nat h1 sinv * SM.qmont_R_inv % S.order));

  qmul_mont_lemma (as_nat h0 s) (as_nat h1 sinv) (as_nat h0 z);
  qmul_mont_lemma (as_nat h0 s) (as_nat h1 sinv) (as_nat h0 r);
  qmul_mont sinv z u1;
  qmul_mont sinv r u2;
  pop_frame ()


inline_for_extraction noextract
val ecdsa_verification_getx: x:felem -> pk:point -> u1:felem -> u2:felem -> Stack bool
  (requires fun h ->
    live h x /\ live h pk /\ live h u1 /\ live h u2 /\
    disjoint x u1 /\ disjoint x u2 /\ disjoint x pk /\
    disjoint pk u1 /\ disjoint pk u2 /\
    point_inv h pk /\ as_nat h u1 < pow2 256 /\ as_nat h u2 < pow2 256)
  (ensures fun h0 b h1 -> modifies (loc x) h0 h1 /\
    as_nat h1 x < S.prime /\
   (let res = S.point_mul_double_g (as_nat h0 u1) (as_nat h0 u2) (as_point_nat h0 pk) in
    let res = S.norm_jacob_point res in
    let (rx, _, _) = res in
    b == not (S.is_point_at_inf res) /\ as_nat h1 x == rx % S.order))

let ecdsa_verification_getx x pk u1 u2 =
  push_frame ();
  let res = create_point () in
  point_mul_double_g res u1 u2 pk;
  norm_jacob_point res res;
  let is_res_point_at_inf = is_point_at_inf_vartime res in
  let res_x = getx res in
  qmod_short res_x x;
  pop_frame ();
  not is_res_point_at_inf


inline_for_extraction
val ecdsa_verification_core:
    alg:S.hash_alg_ecdsa
  -> pk:point
  -> r:felem
  -> s:felem
  -> msg_len:size_t{v msg_len >= S.min_input_length alg}
  -> msg:lbuffer uint8 msg_len
  -> x:felem ->
  Stack bool
  (requires fun h ->
    live h pk /\ live h r /\ live h s /\ live h msg /\ live h x /\
    disjoint pk r /\ disjoint pk s /\ disjoint pk msg /\ disjoint pk x /\
    disjoint x r /\ disjoint x s /\ disjoint x msg /\
    as_nat h s < S.order /\ as_nat h r < S.order /\
    point_inv h pk)
  (ensures fun h0 b h1 -> modifies (loc x) h0 h1 /\
    (let hashM = S.hash_ecdsa alg (v msg_len) (as_seq h0 msg) in
    let z = BSeq.nat_from_bytes_be (LSeq.sub hashM 0 32) % S.order in
    let sinv = S.qinv (as_nat h0 s) in
    let u1 = sinv * z % S.order in
    let u2 = sinv * as_nat h0 r % S.order in
    let rx, ry, rz = S.norm_jacob_point (S.point_mul_double_g u1 u2 (as_point_nat h0 pk)) in
    b == not (S.is_point_at_inf (rx, ry, rz)) /\ as_nat h1 x == rx % S.order))

let ecdsa_verification_core alg pk r s msg_len msg x =
  push_frame ();
  let u1u2z = create 12ul (u64 0) in
  let u1 = sub u1u2z 0ul 4ul in
  let u2 = sub u1u2z 4ul 4ul in
  let z = sub u1u2z 8ul 4ul in
  PS.msg_as_felem alg msg_len msg z;
  ecdsa_verification_get_u12 u1 u2 r s z;
  let r = ecdsa_verification_getx x pk u1 u2 in
  pop_frame ();
  r


inline_for_extraction
val ecdsa_verification:
    alg:S.hash_alg_ecdsa
  -> msg_len:size_t{v msg_len >= S.min_input_length alg}
  -> msg:lbuffer uint8 msg_len
  -> public_key:lbuffer uint8 64ul
  -> signature_r:lbuffer uint8 32ul
  -> signature_s:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h public_key /\ live h signature_r /\ live h signature_s /\ live h msg)
  (ensures fun h0 result h1 -> modifies0 h0 h1 /\
    result == S.ecdsa_verification_agile alg (as_seq h0 public_key)
      (as_seq h0 signature_r) (as_seq h0 signature_s) (v msg_len) (as_seq h0 msg))

let ecdsa_verification alg msg_len msg public_key signature_r signature_s =
  push_frame ();
  let pkrsx = create 24ul (u64 0) in
  let r_q = sub pkrsx 0ul 4ul in
  let s_q = sub pkrsx 4ul 4ul in
  let x = sub pkrsx 8ul 4ul in
  let pk = sub pkrsx 12ul 12ul in

  bn_from_bytes_be4 r_q signature_r;
  bn_from_bytes_be4 s_q signature_s;
  let is_pk_valid = load_point_vartime pk public_key in
  let is_rs_valid = are_r_and_s_valid r_q s_q in

  if not (is_pk_valid && is_rs_valid) then
    begin pop_frame (); false end
  else
    let b = ecdsa_verification_core alg pk r_q s_q msg_len msg x in
    if not b then
      begin pop_frame (); false end
      else
        begin let res = bn_is_eq_vartime4 x r_q in pop_frame (); res end
