module Hacl.Impl.P256.Point

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Math.Lemmas
open FStar.Mul

open Lib.IntTypes
open Lib.ByteBuffer
open Lib.Buffer

open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Spec.P256.Math
open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.RawCmp
open Hacl.Impl.P256.Field
open Hacl.Impl.P256.Finv
open Hacl.Impl.P256.Scalar
open Hacl.Impl.P256.Core
open Hacl.Impl.P256.Constants

module BSeq = Lib.ByteSequence
module S = Spec.P256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@CInline]
let make_base_point p =
  let x = getx p in
  let y = gety p in
  let z = getz p in
  make_g_x x;
  make_g_y y;
  make_fone z


[@CInline]
let make_point_at_inf p =
  let x = getx p in
  let y = gety p in
  let z = getz p in
  make_fzero x;
  make_fzero y;
  make_fzero z


let copy_point p res = copy res p


///  Point conversion between Montgomery and Regular representations

[@CInline]
let point_to_mont p res =
  let px = getx p in
  let py = gety p in
  let pz = getz p in

  let rx = getx res in
  let ry = gety res in
  let rz = getz res in

  toDomain px rx;
  toDomain py ry;
  toDomain pz rz


[@CInline]
let point_from_mont p res =
  let px = getx p in
  let py = gety p in
  let pz = getz p in

  let rx = getx res in
  let ry = gety res in
  let rz = getz res in

  fromDomain px rx;
  fromDomain py ry;
  fromDomain pz rz


///  check if a point is a point-at-infinity

(* https://crypto.stackexchange.com/questions/43869/point-at-infinity-and-error-handling*)
val lemma_mont_is_point_at_inf: p:S.point_nat{let (_, _, z) = p in z < S.prime} ->
  Lemma (S.isPointAtInfinity p == S.isPointAtInfinity (SM.fromDomainPoint p))

let lemma_mont_is_point_at_inf p =
  let px, py, pz = p in
  assert (if S.isPointAtInfinity p then pz == 0 else pz <> 0);
  assert (SM.fromDomain_ pz == pz * SM.mont_R_inv % S.prime);
  assert_norm (SM.mont_R_inv % S.prime <> 0);
  assert_norm (0 * SM.mont_R_inv % S.prime == 0);
  lemma_multiplication_not_mod_prime pz;
  assert (if pz = 0 then SM.fromDomain_ pz == 0 else SM.fromDomain_ pz <> 0)


[@CInline]
let is_point_at_inf p =
  let h0 = ST.get () in
  lemma_mont_is_point_at_inf (as_point_nat (as_seq h0 p));
  let pz = getz p in
  bn_is_zero_mask4 pz


[@CInline]
let is_point_at_inf_vartime p =
  let pz = getz p in
  bn_is_zero_vartime4 pz


///  Point conversion between Jacobian and Affine coordinates representations

inline_for_extraction noextract
val norm_jacob_point_z: p:point -> res:felem -> Stack unit
  (requires fun h ->
    live h res /\ live h p /\ disjoint p res /\
    point_z_as_nat h p < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    (let _, _, rz = S.norm_jacob_point (SM.fromDomainPoint (as_point_nat (as_seq h0 p))) in
    as_nat h1 res == rz))

let norm_jacob_point_z p res =
  push_frame ();
  let fresero = create (size 4) (u64 0) in
  let bit = is_point_at_inf p in

  bn_set_one4 res;
  bn_copy_conditional4 res fresero bit;
  pop_frame ()


[@CInline]
let norm_jacob_point_x p res =
  let px = getx p in
  let pz = getz p in

  let h0 = ST.get () in
  fsqr pz res;       // rx = pz * pz
  let h1 = ST.get () in
  assert (fmont_as_nat h1 res == S.fmul (fmont_as_nat h0 pz) (fmont_as_nat h0 pz));
  finv res res;       // rx = finv rx
  let h2 = ST.get () in
  assert (fmont_as_nat h2 res == S.finv (fmont_as_nat h1 res));
  fmul px res res;    // rx = px * rx
  let h3 = ST.get () in
  assert (fmont_as_nat h3 res == S.fmul (fmont_as_nat h0 px) (fmont_as_nat h2 res));
  fromDomain res res;
  let h4 = ST.get () in
  assert (as_nat h4 res == fmont_as_nat h3 res)


// TODO: rm
inline_for_extraction noextract
val norm_jacob_point_y: p:point -> res:felem -> Stack unit
  (requires fun h ->
    live h res /\ live h p /\ disjoint p res /\
    point_inv (as_seq h p))
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    (let _, ry, _ = S.norm_jacob_point (SM.fromDomainPoint (as_point_nat (as_seq h0 p))) in
    as_nat h1 res == ry))

let norm_jacob_point_y p res =
  let py = gety p in
  let pz = getz p in

  let h0 = ST.get () in
  fcube pz res;       // ry = pz * pz * pz
  let h1 = ST.get () in
  finv res res;       // ry = finv ry
  let h2 = ST.get () in
  assert (fmont_as_nat h2 res == S.finv (fmont_as_nat h1 res));
  fmul py res res;    // ry = px * ry
  let h3 = ST.get () in
  assert (fmont_as_nat h3 res == S.fmul (fmont_as_nat h0 py) (fmont_as_nat h2 res));
  fromDomain res res;
  let h4 = ST.get () in
  assert (as_nat h4 res == fmont_as_nat h3 res)


[@CInline]
let norm_jacob_point p res =
  push_frame ();
  let tmp = create 12ul (u64 0) in
  let tx = getx tmp in
  let ty = gety tmp in
  let tz = getz tmp in
  norm_jacob_point_x p tx;
  norm_jacob_point_y p ty;
  norm_jacob_point_z p tz;
  copy_point tmp res;
  pop_frame ()


[@CInline]
let to_jacob_point p res =
  let px = getx res in
  let py = gety res in
  let pz = getz res in
  copy px (sub p 0ul 4ul);
  copy py (sub p 4ul 4ul);
  bn_set_one4 pz


///  Check if a point is on the curve

let lemmaEraseToDomainFromDomain z =
  lemma_mod_mul_distr_l (z * z) z S.prime


val lemma_norm_as_specification: xD: nat{xD < S.prime} -> yD: nat{yD < S.prime} ->
  zD: nat {zD < S.prime} ->
  x3 : nat {x3 == xD * (S.pow (zD * zD) (S.prime - 2) % S.prime) % S.prime}->
  y3 : nat {y3 == yD * (S.pow (zD * zD * zD) (S.prime -2) % S.prime) % S.prime} ->
  z3: nat {if S.isPointAtInfinity(xD, yD, zD) then z3 == 0 else z3 == 1} ->
  Lemma (
  let (xN, yN, zN) = S.norm_jacob_point (xD, yD, zD) in
  x3 == xN /\ y3 == yN /\ z3 == zN)


let lemma_norm_as_specification xD yD zD x3 y3 z3 =
  power_distributivity (zD * zD * zD) (S.prime - 2) S.prime;
  power_distributivity (zD * zD) (S.prime -2) S.prime


inline_for_extraction noextract
val y_2: y: felem -> r: felem -> Stack unit
  (requires fun h -> as_nat h y < S.prime /\ live h y /\ live h r /\ eq_or_disjoint y r)
  (ensures fun h0 _ h1 -> modifies (loc r) h0 h1 /\ as_nat h1 r == toDomain_ ((as_nat h0 y) * (as_nat h0 y) % S.prime))

let y_2 y r =
  toDomain y r;
  fsqr r r


val lemma_xcube: x_: nat {x_ < S.prime} -> Lemma
  (((x_ * x_ * x_ % S.prime) - (3 * x_ % S.prime)) % S.prime == (x_ * x_ * x_ - 3 * x_) % S.prime)

let lemma_xcube x_ =
  lemma_mod_add_distr (- (3 * x_ % S.prime)) (x_ * x_ * x_) S.prime;
  lemma_mod_sub_distr (x_ * x_ * x_ ) (3 * x_) S.prime


val lemma_xcube2: x_ : nat {x_ < S.prime} -> Lemma (toDomain_ (((((x_ * x_ * x_) - (3 * x_)) % S.prime) + Spec.P256.b_coeff) % S.prime) == toDomain_ ((x_ * x_ * x_  + Spec.P256.a_coeff * x_ + Spec.P256.b_coeff) % S.prime))

let lemma_xcube2 x_ =
  lemma_mod_add_distr Spec.P256.b_coeff ((x_ * x_ * x_) - (3 * x_)) S.prime


inline_for_extraction noextract
val xcube_minus_x: x: felem -> r: felem -> Stack unit
  (requires fun h -> as_nat h x < S.prime /\ live h x  /\ live h r /\ eq_or_disjoint x r)
  (ensures fun h0 _ h1 ->
    modifies (loc r) h0 h1 /\
    (
      let x_ = as_nat h0 x in
      as_nat h1 r = toDomain_((x_ * x_ * x_ - 3 * x_ + Spec.P256.b_coeff) % S.prime))
    )

let xcube_minus_x x r =
  push_frame();
      let h0 = ST.get() in
    let xToDomainBuffer = create (size 4) (u64 0) in
    let minusThreeXBuffer = create (size 4) (u64 0) in
    let p256_constant = create (size 4) (u64 0) in
  toDomain x xToDomainBuffer;
  fsqr xToDomainBuffer r;
  fmul r xToDomainBuffer r;
    lemma_mod_mul_distr_l ((as_nat h0 x) * (as_nat h0 x)) (as_nat h0 x) S.prime;
  fmul_by_3 xToDomainBuffer minusThreeXBuffer;
  fsub r minusThreeXBuffer r;
    make_b_coeff p256_constant;
  fadd r p256_constant r;
  pop_frame();

  let x_ = as_nat h0 x in
  lemma_xcube x_;
  lemma_mod_add_distr Spec.P256.b_coeff ((x_ * x_ * x_) - (3 * x_)) S.prime;
  lemma_xcube2 x_


val lemma_modular_multiplication_p256_2_d: a:nat {a < S.prime} -> b:nat {b < S.prime} ->
  Lemma (toDomain_ a = toDomain_ b <==> a == b)

let lemma_modular_multiplication_p256_2_d a b =
   lemmaToDomain a;
   lemmaToDomain b;
   lemma_modular_multiplication_p256_2 a b


let isPointOnCurvePublic p =
  push_frame();
    let y2Buffer = create (size 4) (u64 0) in
    let xBuffer = create (size 4) (u64 0) in
  let h0 = ST.get() in
    let x = sub p (size 0) (size 4) in
    let y = sub p (size 4) (size 4) in
    y_2 y y2Buffer;
    xcube_minus_x x xBuffer;

    lemma_modular_multiplication_p256_2_d ((as_nat h0 y) * (as_nat h0 y) % S.prime) (let x_ = as_nat h0 x in (x_ * x_ * x_ - 3 * x_ + Spec.P256.b_coeff) % S.prime);

    let r = bn_is_eq_mask4 y2Buffer xBuffer in
    let z = not (eq_0_u64 r) in
  pop_frame();
     z


val isCoordinateValid: p: point -> Stack bool
  (requires fun h -> live h p /\ point_z_as_nat h p == 1)
  (ensures fun h0 r h1 ->
    modifies0 h0 h1 /\
    r == (point_x_as_nat h0 p < S.prime && point_y_as_nat h0 p < S.prime && point_z_as_nat h0 p < S.prime)
  )

let isCoordinateValid p =
  push_frame();
  let tempBuffer = create (size 4) (u64 0) in
  recall_contents prime_buffer (Lib.Sequence.of_list p256_prime_list);
  let x = sub p (size 0) (size 4) in
  let y = sub p (size 4) (size 4) in

  let carryX = bn_sub4_il x prime_buffer tempBuffer in
  let carryY = bn_sub4_il y prime_buffer tempBuffer in

  let lessX = eq_u64_nCT carryX (u64 1) in
  let lessY = eq_u64_nCT carryY (u64 1) in

  let r = lessX && lessY in
  pop_frame();
  r


let verifyQValidCurvePoint pubKeyAsPoint =
  let coordinatesValid = isCoordinateValid pubKeyAsPoint in
  if not coordinatesValid then false else
    let belongsToCurve = isPointOnCurvePublic pubKeyAsPoint in
    coordinatesValid && belongsToCurve


let verifyQ pubKey =
  push_frame();
    let h0 = ST.get() in
    let pubKeyX = sub pubKey (size 0) (size 32) in
    let pubKeyY = sub pubKey (size 32) (size 32) in
    let publicKeyJ = create (size 12) (u64 0) in
    let publicKeyB = create (size 8) (u64 0) in
	let publicKeyX = sub publicKeyB (size 0) (size 4) in
	let publicKeyY = sub publicKeyB (size 4) (size 4) in

    bn_from_bytes_be4 pubKeyX publicKeyX;
    bn_from_bytes_be4 pubKeyY publicKeyY;
  let h1 = ST.get() in
      lemma_core_0 publicKeyX h1;
      BSeq.uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 pubKeyX);
      lemma_core_0 publicKeyY h1;
      BSeq.uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 pubKeyY);

      SD.changeEndianLemma (BSeq.uints_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))));
      BSeq.uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 (gsub pubKey (size 0) (size 32)));

      SD.changeEndianLemma (BSeq.uints_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))));
      BSeq.uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 (gsub pubKey (size 32) (size 32)));

  to_jacob_point publicKeyB publicKeyJ;
  let r = verifyQValidCurvePoint publicKeyJ in
  pop_frame();
  r


let isMoreThanZeroLessThanOrder x =
  push_frame();
    let h0 = ST.get() in
      let xAsFelem = create (size 4) (u64 0) in
      bn_from_bytes_be4 x xAsFelem;
    let h1 = ST.get() in

      lemma_core_0 xAsFelem h1;
      Spec.ECDSA.changeEndianLemma (BSeq.uints_from_bytes_be (as_seq h0 x));
      BSeq.uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 x);

  let tempBuffer = create (size 4) (u64 0) in
    recall_contents primeorder_buffer (Lib.Sequence.of_list p256_order_prime_list);
  let carry = bn_sub4_il xAsFelem primeorder_buffer tempBuffer in
  let less = eq_mask carry (u64 1) in
  let more = bn_is_zero_mask4 xAsFelem in
  let notMore = lognot more in
    lognot_lemma more;
  let result = logand less notMore in
    logand_lemma less notMore;
    lognot_lemma result;

  pop_frame();

  let open Hacl.Impl.P256.RawCmp in
  unsafe_bool_of_u64 (lognot result)
