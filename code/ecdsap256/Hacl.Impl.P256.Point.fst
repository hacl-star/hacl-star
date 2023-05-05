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
  make_fone y;
  make_fzero z


///  Check if a point is a point-at-infinity

(* https://crypto.stackexchange.com/questions/43869/point-at-infinity-and-error-handling*)
val lemma_mont_is_point_at_inf: p:S.proj_point{let (_, _, z) = p in z < S.prime} ->
  Lemma (S.is_point_at_inf p == S.is_point_at_inf (from_mont_point p))

let lemma_mont_is_point_at_inf p =
  let px, py, pz = p in
  SM.lemma_from_mont_zero pz


[@CInline]
let is_point_at_inf p =
  let h0 = ST.get () in
  lemma_mont_is_point_at_inf (as_point_nat h0 p);
  let pz = getz p in
  bn_is_zero_mask4 pz


[@CInline]
let is_point_at_inf_vartime p =
  let h0 = ST.get () in
  lemma_mont_is_point_at_inf (as_point_nat h0 p);
  let pz = getz p in
  bn_is_zero_vartime4 pz


///  Create a copy of a point

let copy_point res p =
  copy res p


///  Point conversion between Projective and Affine coordinates representations

[@CInline]
let to_aff_point res p =
  push_frame ();
  let zinv = create_felem () in
  let px = getx p in
  let py = gety p in
  let pz = getz p in

  let x = aff_getx res in
  let y = aff_gety res in

  FI.finv zinv pz;
  fmul x px zinv;
  fmul y py zinv;
  from_mont x x;
  from_mont y y;
  pop_frame ()


[@CInline]
let to_aff_point_x res p =
  push_frame ();
  let zinv = create_felem () in
  let px = getx p in
  let pz = getz p in

  FI.finv zinv pz;
  fmul res px zinv;
  from_mont res res;
  pop_frame ()


[@CInline]
let to_proj_point res p =
  let px = aff_getx p in
  let py = aff_gety p in

  let rx = getx res in
  let ry = gety res in
  let rz = getz res in
  let h0 = ST.get () in
  SM.lemma_to_from_mont_id (as_nat h0 px);
  SM.lemma_to_from_mont_id (as_nat h0 py);
  to_mont rx px;
  to_mont ry py;
  make_fone rz


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


// y *% y =?= x *% x *% x +% a_coeff *% x +% b_coeff
[@CInline]
let is_on_curve_vartime p =
  push_frame ();
  let rp = create_felem () in
  let tx = create_felem () in
  let ty = create_felem () in
  let px = aff_getx p in
  let py = aff_gety p in
  let h0 = ST.get () in
  to_mont tx px;
  to_mont ty py;

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


[@CInline]
let point_store res p =
  push_frame ();
  let aff_p = create_aff_point () in
  to_aff_point aff_p p;
  aff_point_store res aff_p;
  pop_frame ()


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
let aff_point_load_vartime p b =
  let p_x = sub b 0ul 32ul in
  let p_y = sub b 32ul 32ul in

  let bn_p_x = aff_getx p in
  let bn_p_y = aff_gety p in
  bn_from_bytes_be4 bn_p_x p_x;
  bn_from_bytes_be4 bn_p_y p_y;
  let is_xy_valid = is_xy_valid_vartime p in
  if not is_xy_valid then false
  else is_on_curve_vartime p


[@CInline]
let load_point_vartime p b =
  push_frame ();
  let p_aff = create_aff_point () in
  let res = aff_point_load_vartime p_aff b in
  if res then to_proj_point p p_aff;
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
  to_mont xM x;
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
