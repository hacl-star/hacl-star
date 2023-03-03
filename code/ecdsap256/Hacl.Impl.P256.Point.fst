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


(* https://crypto.stackexchange.com/questions/43869/point-at-infinity-and-error-handling*)
val lemma_pointAtInfInDomain: x: nat -> y: nat -> z: nat {z < S.prime} ->
  Lemma (S.isPointAtInfinity (x, y, z) == S.isPointAtInfinity ((fromDomain_ x), (fromDomain_ y), (fromDomain_ z)))

let lemma_pointAtInfInDomain x y z =
  assert (if S.isPointAtInfinity (x, y, z) then z == 0 else z <> 0);
  assert_norm (S.modp_inv2 (pow2 256) % S.prime <> 0);
  lemmaFromDomain z;
  assert (fromDomain_ z == (z * S.modp_inv2 (pow2 256) % S.prime));
  assert_norm (0 * S.modp_inv2 (pow2 256) % S.prime == 0);
  lemma_multiplication_not_mod_prime z;
  assert (if z = 0 then z * S.modp_inv2 (pow2 256) % S.prime == 0
                   else fromDomain_ z <> 0)


let isPointAtInfinityPrivate p =
  let h0 = ST.get() in
  let z0 = index p (size 8) in
  let z1 = index p (size 9) in
  let z2 = index p (size 10) in
  let z3 = index p (size 11) in
  let z0_zero = eq_mask z0 (u64 0) in
  let z1_zero = eq_mask z1 (u64 0) in
  let z2_zero = eq_mask z2 (u64 0) in
  let z3_zero = eq_mask z3 (u64 0) in
     eq_mask_lemma z0 (u64 0);
     eq_mask_lemma z1 (u64 0);
     eq_mask_lemma z2 (u64 0);
     eq_mask_lemma z3 (u64 0);
  let r = logand(logand z0_zero z1_zero) (logand z2_zero z3_zero) in
    lemma_pointAtInfInDomain (as_nat h0 (gsub p (size 0) (size 4))) (as_nat h0 (gsub p (size 4) (size 4))) (as_nat h0 (gsub p (size 8) (size 4)));
  r


let isPointAtInfinityPublic p =
  let z0 = index p (size 8) in
  let z1 = index p (size 9) in
  let z2 = index p (size 10) in
  let z3 = index p (size 11) in
  let z0_zero = eq_0_u64 z0 in
  let z1_zero = eq_0_u64 z1 in
  let z2_zero = eq_0_u64 z2 in
  let z3_zero = eq_0_u64 z3 in
  z0_zero && z1_zero && z2_zero && z3_zero


let pointToDomain p result =
    let p_x = sub p (size 0) (size 4) in
    let p_y = sub p (size 4) (size 4) in
    let p_z = sub p (size 8) (size 4) in

    let r_x = sub result (size 0) (size 4) in
    let r_y = sub result (size 4) (size 4) in
    let r_z = sub result (size 8) (size 4) in

    toDomain p_x r_x;
    toDomain p_y r_y;
    toDomain p_z r_z


let pointFromDomain p result =
    let p_x = sub p (size 0) (size 4) in
    let p_y = sub p (size 4) (size 4) in
    let p_z = sub p (size 8) (size 4) in

    let r_x = sub result (size 0) (size 4) in
    let r_y = sub result (size 4) (size 4) in
    let r_z = sub result (size 8) (size 4) in

    fromDomain p_x r_x;
    fromDomain p_y r_y;
    fromDomain p_z r_z


inline_for_extraction noextract
val normalisation_update: z2x: felem -> z3y: felem ->p: point ->  resultPoint: point -> Stack unit
  (requires fun h -> live h z2x /\ live h z3y /\ live h resultPoint /\ live h p /\
    as_nat h z2x < S.prime /\ as_nat h z3y < S.prime /\
    as_nat h (gsub p (size 8) (size 4)) < S.prime /\
    disjoint z2x z3y /\ disjoint z2x resultPoint /\ disjoint z3y resultPoint)
  (ensures fun h0 _ h1 -> modifies (loc resultPoint) h0 h1 /\
    (
      let x0 = as_nat h0 (gsub p (size 0) (size 4)) in
      let y0 = as_nat h0 (gsub p (size 4) (size 4)) in
      let z0 = as_nat h0 (gsub p (size 8) (size 4)) in

      let x1 = as_nat h1 (gsub resultPoint (size 0) (size 4)) in
      let y1 = as_nat h1 (gsub resultPoint (size 4) (size 4)) in
      let z1 = as_nat h1 (gsub resultPoint (size 8) (size 4)) in

      x1 == fromDomain_(as_nat h0 z2x) /\ y1 == fromDomain_(as_nat h0 z3y)  /\
      (
	if Spec.P256.isPointAtInfinity (fromDomain_ x0, fromDomain_ y0, fromDomain_ z0) then  z1 == 0 else z1 == 1
      ))
  )


let normalisation_update z2x z3y p resultPoint =
  push_frame();
    let zeroBuffer = create (size 4) (u64 0) in

  let resultX = sub resultPoint (size 0) (size 4) in
  let resultY = sub resultPoint (size 4) (size 4) in
  let resultZ = sub resultPoint (size 8) (size 4) in
    let h0 = ST.get() in
  let bit = isPointAtInfinityPrivate p in
  fromDomain z2x resultX;
  fromDomain z3y resultY;
  bn_set_one4 resultZ;
    let h1 = ST.get() in
  bn_copy_conditional4 resultZ zeroBuffer bit;
    let h2 = ST.get() in
  pop_frame()


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


let norm p resultPoint tempBuffer =
  let xf = sub p (size 0) (size 4) in
  let yf = sub p (size 4) (size 4) in
  let zf = sub p (size 8) (size 4) in


  let z2f = sub tempBuffer (size 4) (size 4) in
  let z3f = sub tempBuffer (size 8) (size 4) in
  let tempBuffer20 = sub tempBuffer (size 12) (size 20) in

    let h0 = ST.get() in
  fsqr zf z2f;
    let h1 = ST.get() in
  fmul z2f zf z3f;
    let h2 = ST.get() in
      lemma_mod_mul_distr_l (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf)) (fromDomain_ (as_nat h0 zf)) S.prime;
      assert (as_nat h1 z2f = toDomain_ (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf) % S.prime));
      assert (as_nat h2 z3f = toDomain_ (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf) % S.prime));

  finv z2f z2f;
    let h3 = ST.get() in
      assert(as_nat h3 z2f = toDomain_ (S.pow (fromDomain_ (as_nat h2 z2f)) (S.prime - 2) % S.prime));
  finv z3f z3f;
    let h4 = ST.get() in
      assert(as_nat h4 z3f = toDomain_ (S.pow (fromDomain_ (as_nat h3 z3f)) (S.prime - 2) % S.prime));

  fmul xf z2f z2f;
  fmul yf z3f z3f;
  normalisation_update z2f z3f p resultPoint;

    let h3 = ST.get() in
    lemmaEraseToDomainFromDomain (fromDomain_ (as_nat h0 zf));
    power_distributivity (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf)) (S.prime -2) S.prime;
    Math.Lemmas.nat_times_nat_is_nat (fromDomain_ (as_nat h0 zf)) (fromDomain_ (as_nat h0 zf));
    Math.Lemmas.nat_times_nat_is_nat (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf)) (fromDomain_ (as_nat h0 zf));
    power_distributivity (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf)) (S.prime -2) S.prime;

    lemma_norm_as_specification (fromDomain_ (point_x_as_nat h0 p)) (fromDomain_ (point_y_as_nat h0 p)) (fromDomain_ (point_z_as_nat h0 p)) (point_x_as_nat h3 resultPoint) (point_y_as_nat h3 resultPoint) (point_z_as_nat h3 resultPoint);

    assert(
       let zD = fromDomain_(point_z_as_nat h0 p) in
       let xD = fromDomain_(point_x_as_nat h0 p) in
       let yD = fromDomain_(point_y_as_nat h0 p) in
       let (xN, yN, zN) = S.norm_jacob_point (xD, yD, zD) in
       point_x_as_nat h3 resultPoint == xN /\ point_y_as_nat h3 resultPoint == yN /\ point_z_as_nat h3 resultPoint == zN)


let normX p result tempBuffer =
  let xf = sub p (size 0) (size 4) in
  let yf = sub p (size 4) (size 4) in
  let zf = sub p (size 8) (size 4) in


  let z2f = sub tempBuffer (size 4) (size 4) in
  let z3f = sub tempBuffer (size 8) (size 4) in
  let tempBuffer20 = sub tempBuffer (size 12) (size 20) in

    let h0 = ST.get() in
  fsqr zf z2f;
  finv z2f z2f;
  fmul z2f xf z2f;
  fromDomain z2f result;
  assert_norm (S.prime >= 2);
    power_distributivity (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf)) (S.prime -2) S.prime



#push-options "--ifuel 1"

let bufferToJac p result =
  let partPoint = sub result (size 0) (size 8) in
  copy partPoint p;
  upd result (size 8) (u64 1);
  upd result (size 9) (u64 0);
  upd result (size 10) (u64 0);
  upd result (size 11) (u64 0)

#pop-options


inline_for_extraction noextract
val y_2: y: felem -> r: felem -> Stack unit
  (requires fun h -> as_nat h y < S.prime /\ live h y /\ live h r /\ eq_or_disjoint y r)
  (ensures fun h0 _ h1 -> modifies (loc r) h0 h1 /\ as_nat h1 r == toDomain_ ((as_nat h0 y) * (as_nat h0 y) % S.prime))

let y_2 y r =
  toDomain y r;
  fsqr r r


inline_for_extraction noextract
val upload_p256_point_on_curve_constant: x: felem -> Stack unit
  (requires fun h -> live h x)
  (ensures fun h0 _ h1 -> modifies (loc x) h0 h1 /\
    as_nat h1 x == toDomain_ Spec.P256.b_coeff /\
    as_nat h1 x < S.prime
 )

let upload_p256_point_on_curve_constant x =
  upd x (size 0) (u64 15608596021259845087);
  upd x (size 1) (u64 12461466548982526096);
  upd x (size 2) (u64 16546823903870267094);
  upd x (size 3) (u64 15866188208926050356);
  assert_norm (
    15608596021259845087 + 12461466548982526096 * pow2 64 +
    16546823903870267094 * pow2 64 * pow2 64 +
    15866188208926050356 * pow2 64 * pow2 64 * pow2 64 == Spec.P256.b_coeff * pow2 256 % S.prime)


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
    upload_p256_point_on_curve_constant p256_constant;
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

  bufferToJac publicKeyB publicKeyJ;
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
