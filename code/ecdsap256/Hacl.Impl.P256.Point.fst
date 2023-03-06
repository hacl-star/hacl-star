module Hacl.Impl.P256.Point

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field
open Hacl.Impl.P256.Finv
open Hacl.Impl.P256.Constants

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
  let open Hacl.Impl.P256.Core in
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
val lemma_mont_is_point_at_inf: p:S.jacob_point{let (_, _, z) = p in z < S.prime} ->
  Lemma (S.is_point_at_inf p == S.is_point_at_inf (SM.fromDomainPoint p))

let lemma_mont_is_point_at_inf p =
  let px, py, pz = p in
  assert (if S.is_point_at_inf p then pz == 0 else pz <> 0);
  assert (SM.fromDomain_ pz == pz * SM.mont_R_inv % S.prime);
  assert_norm (SM.mont_R_inv % S.prime <> 0);
  assert_norm (0 * SM.mont_R_inv % S.prime == 0);
  Hacl.Spec.P256.Math.lemma_multiplication_not_mod_prime pz;
  assert (if pz = 0 then SM.fromDomain_ pz == 0 else SM.fromDomain_ pz <> 0)


[@CInline]
let is_point_at_inf p =
  let h0 = ST.get () in
  lemma_mont_is_point_at_inf (as_point_nat h0 p);
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
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    (let _, _, rz = S.norm_jacob_point (SM.fromDomainPoint (as_point_nat h0 p)) in
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
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    (let _, ry, _ = S.norm_jacob_point (SM.fromDomainPoint (as_point_nat h0 p)) in
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
  let px = aff_getx p in
  let py = aff_gety p in

  let rx = getx res in
  let ry = gety res in
  let rz = getz res in
  copy rx px;
  copy ry py;
  bn_set_one4 rz


///  Check if a point is on the curve

inline_for_extraction noextract
val compute_rp_ec_equation: x:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ disjoint x res /\
    as_nat h x < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\ (let x = fmont_as_nat h0 x in
    fmont_as_nat h1 res ==
      S.fadd (S.fadd (S.fmul (S.fmul x x) x) (S.fmul S.a_coeff x)) S.b_coeff))

let compute_rp_ec_equation x res =
  push_frame ();
  let tmp = create 4ul (u64 0) in
  fcube x res;
  make_a_coeff tmp;
  fmul tmp x tmp;
  fadd res tmp res;
  make_b_coeff tmp;
  fadd res tmp res;
  pop_frame ()


// y *% y = x *% x *% x +% a_coeff *% x +% b_coeff
[@CInline]
let is_point_on_curve_vartime p =
  push_frame ();
  let rp = create 4ul (u64 0) in
  let tx = create 4ul (u64 0) in
  let ty = create 4ul (u64 0) in
  let px = aff_getx p in
  let py = aff_gety p in
  Hacl.Impl.P256.Core.toDomain px tx;
  Hacl.Impl.P256.Core.toDomain py ty;

  fsqr ty ty;
  compute_rp_ec_equation tx rp;
  let r = bn_is_eq_mask4 ty rp in admit();
  pop_frame ();
  Hacl.Bignum.Base.unsafe_bool_of_limb r


//-------------------------

[@CInline]
let aff_store_point res p =
  let px = aff_getx p in
  let py = aff_gety p in

  let h0 = ST.get () in
  update_sub_f h0 res 0ul 32ul
    (fun h -> BSeq.nat_to_bytes_be 32 (as_nat h0 px))
    (fun _ -> bn_to_bytes_be4 px (sub res 0ul 32ul));

  let h1 = ST.get () in
  update_sub_f h1 res 32ul 32ul
    (fun h -> BSeq.nat_to_bytes_be 32 (as_nat h1 py))
    (fun _ -> bn_to_bytes_be4 py (sub res 32ul 32ul));

  let h2 = ST.get () in
  let px = Ghost.hide (BSeq.nat_to_bytes_be 32 (as_nat h0 px)) in
  let py = Ghost.hide (BSeq.nat_to_bytes_be 32 (as_nat h0 py)) in
  LSeq.eq_intro (as_seq h2 res) (LSeq.concat #_ #32 #32 px py)


inline_for_extraction noextract
val is_xy_valid: p:aff_point -> Stack bool
  (requires fun h -> live h p)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    r == (aff_point_x_as_nat h0 p < S.prime &&
          aff_point_y_as_nat h0 p < S.prime))

let is_xy_valid p =
  let px = aff_getx p in
  let py = aff_gety p in
  let lessX = bn_is_lt_prime_mask4 px in
  let lessY = bn_is_lt_prime_mask4 py in
  let res = logand lessX lessY in
  logand_lemma lessX lessY;
  Hacl.Bignum.Base.unsafe_bool_of_limb res


[@CInline]
let load_point_vartime p b =
  push_frame ();
  let p_x = sub b 0ul 32ul in
  let p_y = sub b 32ul 32ul in
  let point_aff = create 8ul (u64 0) in
  let bn_p_x = aff_getx point_aff in
  let bn_p_y = aff_gety point_aff in
  bn_from_bytes_be4 p_x bn_p_x;
  bn_from_bytes_be4 p_y bn_p_y;
  let is_xy_valid = is_xy_valid point_aff in
  let res = if not is_xy_valid then false else is_point_on_curve_vartime point_aff in
  if res then
    to_jacob_point point_aff p;
  pop_frame ();
  res


let validate_pubkey pk =
  push_frame ();
  let point_jac = create 12ul (u64 0) in
  let res = load_point_vartime point_jac pk in
  pop_frame ();
  res


[@CInline]
let isMoreThanZeroLessThanOrder x =
  push_frame ();
  let bn_x = create 4ul (u64 0) in
  bn_from_bytes_be4 x bn_x;
  let h0 = ST.get () in
  let is_bn_x_lt_order = Hacl.Impl.P256.Scalar.bn_is_lt_order_mask4 bn_x in
  assert (v is_bn_x_lt_order = (if as_nat h0 bn_x < S.order then ones_v U64 else 0));
  let is_bn_x_eq_zero = bn_is_zero_mask4 bn_x in
  assert (v is_bn_x_eq_zero = (if as_nat h0 bn_x = 0 then ones_v U64 else 0));
  lognot_lemma is_bn_x_eq_zero;
  assert (v (lognot is_bn_x_eq_zero) = (if 0 < as_nat h0 bn_x then ones_v U64 else 0));

  let res = logand is_bn_x_lt_order (lognot is_bn_x_eq_zero) in
  logand_lemma is_bn_x_lt_order (lognot is_bn_x_eq_zero);
  assert (v res == (if 0 < as_nat h0 bn_x && as_nat h0 bn_x < S.order then ones_v U64 else 0));
  pop_frame ();
  Hacl.Bignum.Base.unsafe_bool_of_limb res
