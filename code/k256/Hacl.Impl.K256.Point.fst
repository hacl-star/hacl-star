module Hacl.Impl.K256.Point

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.K256
module SL = Spec.K256.Lemmas
module BI = Hacl.Spec.K256.Field52
module BL = Hacl.Spec.K256.Field52.Lemmas

open Hacl.K256.Field
open Hacl.Impl.K256.Finv

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Create a point

let create_aff_point () =
  create 10ul (u64 0)


let create_point () =
  create (3ul *! 5ul) (u64 0)


let make_point_at_inf p =
  SL.to_aff_point_at_infinity_lemma ();
  let px, py, pz = getx p, gety p, getz p in
  set_zero px;
  set_one py;
  set_zero pz


let make_g g =
  let gx, gy, gz = getx g, gety g, getz g in

  [@inline_let]
  let x =
   (u64 0x2815b16f81798,
    u64 0xdb2dce28d959f,
    u64 0xe870b07029bfc,
    u64 0xbbac55a06295c,
    u64 0x79be667ef9dc) in

  assert_norm (0x79be667ef9dc < max48);
  assert_norm (0xe1108a8fd17b4 < max52);
  assert_norm (S.g_x == as_nat5 x);
  make_u52_5 gx x;

  [@inline_let]
  let y =
   (u64 0x7d08ffb10d4b8,
    u64 0x48a68554199c4,
    u64 0xe1108a8fd17b4,
    u64 0xc4655da4fbfc0,
    u64 0x483ada7726a3) in

  assert_norm (S.g_y == as_nat5 y);
  make_u52_5 gy y;

  set_one gz


let copy_point out p =
  let px, py, pz = getx p, gety p, getz p in
  let ox, oy, oz = getx out, gety out, getz out in
  copy_felem ox px;
  copy_felem oy py;
  copy_felem oz pz


///  Conversion functions between affine and projective coordinates

let to_proj_point p p_aff =
  let x, y = aff_getx p_aff, aff_gety p_aff in
  let x1, y1, z1 = getx p, gety p, getz p in
  copy x1 x;
  copy y1 y;
  set_one z1


[@CInline]
let to_aff_point p_aff p =
  push_frame ();
  let x, y = aff_getx p_aff, aff_gety p_aff in
  let x1, y1, z1 = getx p, gety p, getz p in
  let zinv = create_felem () in
  finv zinv z1;
  fmul x x1 zinv;
  fmul y y1 zinv;
  let h = ST.get () in
  assert (inv_lazy_reduced2 h x);
  assert (inv_lazy_reduced2 h y);

  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h x);
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h y);
  fnormalize x x;
  fnormalize y y;
  pop_frame ()


[@CInline]
let to_aff_point_x x p =
  push_frame ();
  let x1, z1 = getx p, getz p in
  let zinv = create_felem () in
  finv zinv z1;
  fmul x x1 zinv;
  let h = ST.get () in
  assert (inv_lazy_reduced2 h x);
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h x);
  fnormalize x x;
  pop_frame ()


///  Is a point in affine coordinates on the curve

inline_for_extraction noextract
val compute_expected_y2 (y2 x:felem) : Stack unit
  (requires fun h ->
    live h x /\ live h y2 /\ disjoint x y2 /\
    inv_fully_reduced h x)
  (ensures  fun h0 _ h1 -> modifies (loc y2) h0 h1 /\
   (let xn = as_nat h0 x in inv_fully_reduced h1 y2 /\
   as_nat h1 y2 == S.fadd (S.fmul (S.fmul xn xn) xn) S.b))

let compute_expected_y2 y2 x =
  push_frame ();
  let b = create_felem () in
  make_u52_5 b (make_b_k256 ());
  let h0 = ST.get () in
  assert (inv_fully_reduced h0 b /\ as_nat h0 b = S.b);

  fsqr y2 x;
  fmul y2 y2 x;
  let h1 = ST.get () in
  assert (inv_lazy_reduced2 h1 y2);
  assert (let xn = as_nat h0 x in
    feval h1 y2 == S.fmul (S.fmul xn xn) xn);

  BL.fadd5_lemma (1,1,1,1,2) (1,1,1,1,1) (as_felem5 h1 y2) (as_felem5 h1 b);
  fadd y2 y2 b;
  let h1 = ST.get () in
  assert (felem_fits5 (as_felem5 h1 y2) (2,2,2,2,3));

  fnormalize y2 y2;
  BL.normalize5_lemma (2,2,2,2,3) (as_felem5 h1 y2);
  pop_frame ()


inline_for_extraction noextract
val is_y_sqr_is_y2_vartime (y2 y:felem) : Stack bool
  (requires fun h ->
    live h y /\ live h y2 /\ disjoint y y2 /\
    inv_fully_reduced h y2 /\ inv_fully_reduced h y)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == (as_nat h0 y2 = S.fmul (as_nat h0 y) (as_nat h0 y)))

let is_y_sqr_is_y2_vartime y2 y =
  push_frame ();
  let y2_comp = create_felem () in

  fsqr y2_comp y;
  let h0 = ST.get () in
  assert (inv_lazy_reduced2 h0 y2);
  fnormalize y2_comp y2_comp;
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h0 y2_comp);

  let res = is_felem_eq_vartime y2 y2_comp in
  pop_frame ();
  res


[@CInline]
let is_on_curve_vartime p =
  push_frame ();
  let y2_exp = create_felem () in
  let x, y = aff_getx p, aff_gety p in
  compute_expected_y2 y2_exp x;
  let res = is_y_sqr_is_y2_vartime y2_exp y in
  pop_frame ();
  res


let is_proj_point_at_inf_vartime p =
  push_frame ();
  let tmp = create_felem () in
  let pz = getz p in

  let h0 = ST.get () in
  assert (inv_lazy_reduced2 h0 (gsub p 10ul 5ul));
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h0 pz);
  fnormalize tmp pz;
  let b = is_felem_zero_vartime tmp in
  pop_frame ();
  b


///  Point negation

[@CInline]
let point_negate out p =
  let h0 = ST.get () in
  let px, py, pz = getx p, gety p, getz p in
  let ox, oy, oz = getx out, gety out, getz out in
  copy_felem ox px;
  copy_felem oz pz;

  BL.fnegate5_lemma (1,1,1,1,2) (as_felem5 h0 py) (u64 2);
  make_u52_5 oy (BI.fnegate5 (py.(0ul), py.(1ul), py.(2ul), py.(3ul), py.(4ul)) (u64 2));
  let h1 = ST.get () in
  assert (felem_fits5 (as_felem5 h1 oy) (4,4,4,4,4));
  assert (as_nat h1 oy == 4 * S.prime - as_nat h0 py);
  BL.normalize_weak5_lemma (4,4,4,4,4) (as_felem5 h1 oy);
  fnormalize_weak oy oy;
  let h2 = ST.get () in
  assert (feval h2 ox == feval h0 px);
  assert (feval h2 oz == feval h0 pz);
  assert (feval h2 oy == (4 * S.prime - as_nat h0 py) % S.prime);
  Math.Lemmas.modulo_addition_lemma (- as_nat h0 py) S.prime 4;
  Math.Lemmas.lemma_mod_sub_distr 0 (as_nat h0 py) S.prime;
  assert (feval h2 oy == (- feval h0 py) % S.prime)


[@CInline]
let point_negate_conditional_vartime p is_negate =
  if is_negate then point_negate p p


///  Point load and store functions

[@CInline]
let aff_point_store out p =
  let px = aff_getx p in
  let py = aff_gety p in

  let h0 = ST.get () in
  update_sub_f h0 out 0ul 32ul
    (fun h -> BSeq.nat_to_bytes_be 32 (as_nat h0 px))
    (fun _ -> store_felem (sub out 0ul 32ul) px);

  let h1 = ST.get () in
  update_sub_f h1 out 32ul 32ul
    (fun h -> BSeq.nat_to_bytes_be 32 (as_nat h1 py))
    (fun _ -> store_felem (sub out 32ul 32ul) py);

  let h2 = ST.get () in
  let px = Ghost.hide (BSeq.nat_to_bytes_be 32 (as_nat h0 px)) in
  let py = Ghost.hide (BSeq.nat_to_bytes_be 32 (as_nat h0 py)) in
  LSeq.eq_intro (as_seq h2 out) (LSeq.concat #_ #32 #32 px py)


[@CInline]
let point_store out p =
  push_frame ();
  let p_aff = create_aff_point () in
  to_aff_point p_aff p;
  aff_point_store out p_aff;
  pop_frame ()


[@CInline]
let aff_point_load_vartime p b =
  let px = sub b 0ul 32ul in
  let py = sub b 32ul 32ul in
  let bn_px = aff_getx p in
  let bn_py = aff_gety p in

  let h0 = ST.get () in
  let is_x_valid = load_felem_lt_prime_vartime bn_px px in
  let is_y_valid = load_felem_lt_prime_vartime bn_py py in
  let h1 = ST.get () in
  assert (as_nat h1 bn_px == BSeq.nat_from_bytes_be (as_seq h0 (gsub b 0ul 32ul)));
  assert (as_nat h1 bn_py == BSeq.nat_from_bytes_be (as_seq h0 (gsub b 32ul 32ul)));
  assert (inv_lazy_reduced1 h1 bn_px);
  assert (inv_lazy_reduced1 h1 bn_py);

  if is_x_valid && is_y_valid then begin
    assert (inv_fully_reduced h1 bn_px);
    assert (inv_fully_reduced h1 bn_py);
    is_on_curve_vartime p end
  else false


[@CInline]
let load_point_vartime p b =
  push_frame ();
  let p_aff = create_aff_point () in
  let res = aff_point_load_vartime p_aff b in
  if res then to_proj_point p p_aff;
  pop_frame ();
  res


let load_point_nocheck out b =
  push_frame ();
  let p_aff = create_aff_point () in
  let px, py = aff_getx p_aff, aff_gety p_aff in
  let pxb = sub b 0ul 32ul in
  let pyb = sub b 32ul 32ul in
  load_felem px pxb;
  load_felem py pyb;
  to_proj_point out p_aff;
  pop_frame ()


inline_for_extraction noextract
val recover_y_vartime_candidate (y x:felem) : Stack bool
  (requires fun h ->
    live h x /\ live h y /\ disjoint x y /\
    inv_fully_reduced h x)
  (ensures fun h0 b h1 -> modifies (loc y) h0 h1 /\ inv_fully_reduced h1 y /\
   (let x = as_nat h0 x in
    let y2 = S.(x *% x *% x +% b) in
    as_nat h1 y == S.fsqrt y2 /\ (b <==> (S.fmul (as_nat h1 y) (as_nat h1 y) == y2))))

let recover_y_vartime_candidate y x =
  push_frame ();
  let y2 = create_felem () in
  compute_expected_y2 y2 x; //y2 = x *% x *% x +% b
  fsqrt y y2;
  let h = ST.get () in
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h y);
  fnormalize y y;

  let is_y_valid = is_y_sqr_is_y2_vartime y2 y in
  pop_frame ();
  is_y_valid


inline_for_extraction noextract
val recover_y_vartime (y x:felem) (is_odd:bool) : Stack bool
  (requires fun h ->
    live h x /\ live h y /\ disjoint x y /\
    inv_fully_reduced h x)
  (ensures fun h0 b h1 -> modifies (loc y) h0 h1 /\ inv_fully_reduced h1 y /\
    (b <==> Some? (S.recover_y (as_nat h0 x) is_odd)) /\
    (b ==> (as_nat h1 y == Some?.v (S.recover_y (as_nat h0 x) is_odd))))

let recover_y_vartime y x is_odd =
  let is_y_valid = recover_y_vartime_candidate y x in
  if not is_y_valid then false
  else begin
    let is_y_odd = is_fodd_vartime y in
    fnegate_conditional_vartime y (is_y_odd <> is_odd);
    true end


[@CInline]
let aff_point_decompress_vartime x y s =
  let s0 = s.(0ul) in
  let s0 = Lib.RawIntTypes.u8_to_UInt8 s0 in
  if not (s0 = 0x02uy || s0 = 0x03uy) then false
  else begin
    let xb = sub s 1ul 32ul in
    let is_x_valid = load_felem_lt_prime_vartime x xb in
    let is_y_odd = s0 = 0x03uy in

    if not is_x_valid then false
    else recover_y_vartime y x is_y_odd end
