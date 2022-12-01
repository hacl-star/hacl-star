module Hacl.Impl.Ed25519.PointConstants

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

module F51 = Hacl.Impl.Ed25519.Field51
module S51 = Hacl.Spec.Curve25519.Field51.Definition

module S = Spec.Ed25519

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val make_point_inf:
  b:lbuffer uint64 20ul ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    F51.point_inv_t h1 b /\ F51.inv_ext_point (as_seq h1 b) /\
    S.to_aff_point (F51.point_eval h1 b) == S.aff_point_at_infinity)

let make_point_inf b =
  let x = getx b in
  let y = gety b in
  let z = getz b in
  let t = gett b in
  make_zero x;
  make_one y;
  make_one z;
  make_zero t;
  let h1 = ST.get () in
  assert (F51.point_eval h1 b == S.point_at_infinity);
  Spec.Ed25519.Lemmas.to_aff_point_at_infinity_lemma ()


inline_for_extraction noextract
val make_g: g:point -> Stack unit
  (requires fun h -> live h g)
  (ensures fun h0 _ h1 -> modifies (loc g) h0 h1 /\
    F51.point_inv_t h1 g /\ F51.inv_ext_point (as_seq h1 g) /\
    F51.point_eval h1 g == S.g)

let make_g g =
  let gx = getx g in
  let gy = gety g in
  let gz = getz g in
  let gt = gett g in

  [@inline_let] let (x0, x1, x2, x3, x4) =
    (u64 0x00062d608f25d51a,
     u64 0x000412a4b4f6592a,
     u64 0x00075b7171a4b31d,
     u64 0x0001ff60527118fe,
     u64 0x000216936d3cd6e5) in

  [@inline_let] let (y0, y1, y2, y3, y4) =
    (u64 0x0006666666666658,
     u64 0x0004cccccccccccc,
     u64 0x0001999999999999,
     u64 0x0003333333333333,
     u64 0x0006666666666666) in

  [@inline_let] let (t0, t1, t2, t3, t4) =
    (u64 0x00068ab3a5b7dda3,
     u64 0x00000eea2a5eadbb,
     u64 0x0002af8df483c27e,
     u64 0x000332b375274732,
     u64 0x00067875f0fd78b7) in

  make_u64_5 gx x0 x1 x2 x3 x4;
  make_u64_5 gy y0 y1 y2 y3 y4;
  make_one gz;
  make_u64_5 gt t0 t1 t2 t3 t4;

  (**) assert_norm (Spec.Ed25519.g_x ==
    S51.as_nat5 (x0, x1, x2, x3, x4) % Spec.Curve25519.prime);
  (**) assert_norm (Spec.Ed25519.g_y ==
    S51.as_nat5 (y0, y1, y2, y3, y4) % Spec.Curve25519.prime);
  (**) assert_norm (Mktuple4?._4 Spec.Ed25519.g ==
    S51.as_nat5 (t0, t1, t2, t3, t4) % Spec.Curve25519.prime);
  let h1 = ST.get () in
  assert (F51.point_inv_t h1 g);
  assert (F51.point_eval h1 g == Spec.Ed25519.g);
  Spec.Ed25519.Lemmas.g_is_on_curve ()
