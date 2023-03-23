module Hacl.Impl.P256.Point

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field
open Hacl.Impl.P256.Constants

module S = Spec.P256
module SM = Hacl.Spec.P256.Montgomery
module FI = Hacl.Impl.P256.Finv

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Create a point

let create_aff_point () =
  create 8ul (u64 0)


let create_point () =
  create 12ul (u64 0)


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


///  Check if a point is a point-at-infinity

(* https://crypto.stackexchange.com/questions/43869/point-at-infinity-and-error-handling*)
val lemma_mont_is_point_at_inf: p:S.jacob_point{let (_, _, z) = p in z < S.prime} ->
  Lemma (S.is_point_at_inf p == S.is_point_at_inf (from_mont_point p))

let lemma_mont_is_point_at_inf p =
  let px, py, pz = p in
  assert (if S.is_point_at_inf p then pz == 0 else pz <> 0);
  assert (SM.from_mont pz == pz * SM.fmont_R_inv % S.prime);
  assert_norm (SM.fmont_R_inv % S.prime <> 0);
  assert_norm (0 * SM.fmont_R_inv % S.prime == 0);
  SM.lemma_from_mont_zero pz;
  assert (if pz = 0 then SM.from_mont pz == 0 else SM.from_mont pz <> 0)


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


///  Create a copy of a point

let copy_point res p =
  copy res p


[@CInline]
let copy_point_conditional res p q_mask =
  let z = getz q_mask in
  let mask = is_point_at_inf q_mask in
  let px = getx p in
  let py = gety p in
  let pz = getz p in

  let rx = getx res in
  let ry = gety res in
  let rz = getz res in

  bn_copy_conditional4 rx mask rx px;
  bn_copy_conditional4 ry mask ry py;
  bn_copy_conditional4 rz mask rz pz


///  Point conversion between Montgomery and Regular representations

[@CInline]
let point_to_mont res p =
  let open Hacl.Impl.P256.Core in
  let px = getx p in
  let py = gety p in
  let pz = getz p in

  let rx = getx res in
  let ry = gety res in
  let rz = getz res in

  to_mont rx px;
  to_mont ry py;
  to_mont rz pz


[@CInline]
let point_from_mont res p =
  let px = getx p in
  let py = gety p in
  let pz = getz p in

  let rx = getx res in
  let ry = gety res in
  let rz = getz res in

  from_mont rx px;
  from_mont ry py;
  from_mont rz pz


///  Point conversion between Jacobian and Affine coordinates representations

inline_for_extraction noextract
val norm_jacob_point_z: res:felem -> p:point -> Stack unit
  (requires fun h ->
    live h res /\ live h p /\ disjoint p res /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    (let _, _, rz = S.norm_jacob_point (from_mont_point (as_point_nat h0 p)) in
    as_nat h1 res == rz))

let norm_jacob_point_z res p =
  push_frame ();
  let zero = create_felem () in
  let bit = is_point_at_inf p in

  bn_set_one4 res;
  bn_copy_conditional4 res bit res zero;
  pop_frame ()


[@CInline]
let norm_jacob_point_x res p =
  let px = getx p in
  let pz = getz p in

  let h0 = ST.get () in
  fsqr res pz;       // rx = pz * pz
  let h1 = ST.get () in
  assert (fmont_as_nat h1 res == S.fmul (fmont_as_nat h0 pz) (fmont_as_nat h0 pz));
  FI.finv res res;       // rx = finv rx
  let h2 = ST.get () in
  assert (fmont_as_nat h2 res == S.finv (fmont_as_nat h1 res));
  fmul res px res;    // rx = px * rx
  let h3 = ST.get () in
  assert (fmont_as_nat h3 res == S.fmul (fmont_as_nat h0 px) (fmont_as_nat h2 res));
  from_mont res res;
  let h4 = ST.get () in
  assert (as_nat h4 res == fmont_as_nat h3 res)


// TODO: rm
inline_for_extraction noextract
val norm_jacob_point_y: res:felem -> p:point -> Stack unit
  (requires fun h ->
    live h res /\ live h p /\ disjoint p res /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    (let _, ry, _ = S.norm_jacob_point (from_mont_point (as_point_nat h0 p)) in
    as_nat h1 res == ry))

let norm_jacob_point_y res p =
  let py = gety p in
  let pz = getz p in

  let h0 = ST.get () in
  fcube res pz;       // ry = pz * pz * pz
  let h1 = ST.get () in
  FI.finv res res;       // ry = finv ry
  let h2 = ST.get () in
  assert (fmont_as_nat h2 res == S.finv (fmont_as_nat h1 res));
  fmul res py res;    // ry = px * ry
  let h3 = ST.get () in
  assert (fmont_as_nat h3 res == S.fmul (fmont_as_nat h0 py) (fmont_as_nat h2 res));
  from_mont res res;
  let h4 = ST.get () in
  assert (as_nat h4 res == fmont_as_nat h3 res)


[@CInline]
let norm_jacob_point res p =
  push_frame ();
  let tmp = create_point () in
  let tx = getx tmp in
  let ty = gety tmp in
  let tz = getz tmp in
  norm_jacob_point_x tx p;
  norm_jacob_point_y ty p;
  norm_jacob_point_z tz p;
  copy_point res tmp;
  pop_frame ()


[@CInline]
let to_jacob_point res p =
  let px = aff_getx p in
  let py = aff_gety p in

  let rx = getx res in
  let ry = gety res in
  let rz = getz res in
  copy rx px;
  copy ry py;
  bn_set_one4 rz


///  Point comparison

inline_for_extraction noextract
val is_point_strong_eq_vartime: p:point -> q:point -> Stack bool
  (requires fun h -> live h p /\ live h q)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r ==
     (point_x_as_nat h0 p = point_x_as_nat h0 q &&
      point_y_as_nat h0 p = point_y_as_nat h0 q &&
      point_z_as_nat h0 p = point_z_as_nat h0 q))

let is_point_strong_eq_vartime p q =
  let px = getx p in
  let py = gety p in
  let pz = getz p in

  let qx = getx q in
  let qy = gety q in
  let qz = getz q in

  let is_x_eq = bn_is_eq_vartime4 px qx in
  let is_y_eq = bn_is_eq_vartime4 py qy in
  let is_z_eq = bn_is_eq_vartime4 pz qz in
  is_x_eq && is_y_eq && is_z_eq


// TODO: avoid calling norm_jacob_point
[@CInline]
let is_point_eq_vartime p q =
  push_frame ();
  let p_norm = create_point () in
  let q_norm = create_point () in

  norm_jacob_point p_norm p;
  norm_jacob_point q_norm q;
  let is_pq_equal = is_point_strong_eq_vartime p_norm q_norm in
  pop_frame ();
  is_pq_equal


///  Check if a point is on the curve

inline_for_extraction noextract
val compute_rp_ec_equation: x:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ disjoint x res /\
    as_nat h x < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\ as_nat h1 res < S.prime /\
    (let x = fmont_as_nat h0 x in
    fmont_as_nat h1 res ==
      S.fadd (S.fadd (S.fmul (S.fmul x x) x) (S.fmul S.a_coeff x)) S.b_coeff))

let compute_rp_ec_equation x res =
  push_frame ();
  let tmp = create_felem () in
  fcube res x;
  make_a_coeff tmp;
  fmul tmp tmp x;
  fadd res tmp res;
  make_b_coeff tmp;
  fadd res tmp res;
  pop_frame ()


inline_for_extraction noextract
val is_y_sqr_is_y2_vartime (y2 y:felem) : Stack bool
  (requires fun h ->
    live h y /\ live h y2 /\ disjoint y y2 /\
    as_nat h y2 < S.prime /\ as_nat h y < S.prime)
  (ensures fun h0 b h1 -> modifies (loc y) h0 h1 /\
    b == (fmont_as_nat h0 y2 = S.fmul (fmont_as_nat h0 y) (fmont_as_nat h0 y)))

let is_y_sqr_is_y2_vartime y2 y =
  fsqr y y; // y = y * y
  let r = feq_mask y y2 in
  Hacl.Bignum.Base.unsafe_bool_of_limb r


// y *% y = x *% x *% x +% a_coeff *% x +% b_coeff
[@CInline]
let is_point_on_curve_vartime p =
  push_frame ();
  let rp = create_felem () in
  let tx = create_felem () in
  let ty = create_felem () in
  let px = aff_getx p in
  let py = aff_gety p in
  let h0 = ST.get () in
  Hacl.Impl.P256.Core.to_mont tx px;
  Hacl.Impl.P256.Core.to_mont ty py;

  SM.lemma_to_from_mont_id (as_nat h0 px);
  SM.lemma_to_from_mont_id (as_nat h0 py);
  compute_rp_ec_equation tx rp;
  let r = is_y_sqr_is_y2_vartime rp ty in
  pop_frame ();
  r


///  Point load and store functions

[@CInline]
let aff_point_store res p =
  let px = aff_getx p in
  let py = aff_gety p in
  bn2_to_bytes_be4 res px py


inline_for_extraction noextract
val is_xy_valid_vartime: p:aff_point -> Stack bool
  (requires fun h -> live h p)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    r == (aff_point_x_as_nat h0 p < S.prime &&
          aff_point_y_as_nat h0 p < S.prime))

let is_xy_valid_vartime p =
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
  let point_aff = create_aff_point () in
  let bn_p_x = aff_getx point_aff in
  let bn_p_y = aff_gety point_aff in
  bn_from_bytes_be4 bn_p_x p_x;
  bn_from_bytes_be4 bn_p_y p_y;
  let is_xy_valid = is_xy_valid_vartime point_aff in
  let res = if not is_xy_valid then false else is_point_on_curve_vartime point_aff in
  if res then
    to_jacob_point p point_aff;
  pop_frame ();
  res


inline_for_extraction noextract
val recover_y_vartime_candidate (y x:felem) : Stack bool
  (requires fun h ->
    live h x /\ live h y /\ disjoint x y /\ as_nat h x < S.prime)
  (ensures fun h0 b h1 -> modifies (loc y) h0 h1 /\ as_nat h1 y < S.prime /\
   (let x = as_nat h0 x in
    let y2 = S.(x *% x *% x +% a_coeff *% x +% b_coeff) in
    as_nat h1 y == S.fsqrt y2 /\ (b <==> (S.fmul (as_nat h1 y) (as_nat h1 y) == y2))))

let recover_y_vartime_candidate y x =
  push_frame ();
  let y2M = create_felem () in
  let xM = create_felem () in
  let yM = create_felem () in
  let h0 = ST.get () in
  SM.lemma_to_from_mont_id (as_nat h0 x);
  Hacl.Impl.P256.Core.to_mont xM x;
  compute_rp_ec_equation xM y2M; // y2M = x *% x *% x +% S.a_coeff *% x +% S.b_coeff
  FI.fsqrt yM y2M; // yM = fsqrt y2M
  let h1 = ST.get () in
  from_mont y yM;
  let is_y_valid = is_y_sqr_is_y2_vartime y2M yM in
  pop_frame ();
  is_y_valid


inline_for_extraction noextract
val recover_y_vartime (y x:felem) (is_odd:bool) : Stack bool
  (requires fun h ->
    live h x /\ live h y /\ disjoint x y /\ as_nat h x < S.prime)
  (ensures fun h0 b h1 -> modifies (loc y) h0 h1 /\
    (b <==> Some? (S.recover_y (as_nat h0 x) is_odd)) /\
    (b ==> (as_nat h1 y < S.prime/\
      as_nat h1 y == Some?.v (S.recover_y (as_nat h0 x) is_odd))))

let recover_y_vartime y x is_odd =
  let is_y_valid = recover_y_vartime_candidate y x in
  if not is_y_valid then false
  else begin
    let is_y_odd = bn_is_odd4 y in
    let is_y_odd = Lib.RawIntTypes.u64_to_UInt64 is_y_odd =. 1uL in
    fnegate_conditional_vartime y (is_y_odd <> is_odd);
    true end


[@CInline]
let aff_point_decompress_vartime x y s =
  let s0 = s.(0ul) in
  let s0 = Lib.RawIntTypes.u8_to_UInt8 s0 in
  if not (s0 = 0x02uy || s0 = 0x03uy) then false
  else begin
    let xb = sub s 1ul 32ul in
    bn_from_bytes_be4 x xb;
    let is_x_valid = bn_is_lt_prime_mask4 x in
    let is_x_valid = Hacl.Bignum.Base.unsafe_bool_of_limb is_x_valid in
    let is_y_odd = s0 = 0x03uy in

    if not is_x_valid then false
    else recover_y_vartime y x is_y_odd end
