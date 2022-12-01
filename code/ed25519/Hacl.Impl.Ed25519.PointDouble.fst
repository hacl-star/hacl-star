module Hacl.Impl.Ed25519.PointDouble

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

module F51 = Hacl.Impl.Ed25519.Field51
module SC = Spec.Curve25519

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val point_double_step_1: p:point -> tmp:lbuffer uint64 20ul -> Stack unit
  (requires fun h ->
    live h p /\ live h tmp /\ disjoint p tmp /\
    F51.point_inv_t h p)
  (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
    (let x1, y1, z1, t1 = F51.point_eval h0 p in
    let a = x1 `SC.fmul` x1 in
    let b = y1 `SC.fmul` y1 in
    let c = 2 `SC.fmul` (z1 `SC.fmul` z1) in
    let h = a `SC.fadd` b in
    let g = a `SC.fsub` b in
    F51.felem_fits h1 (gsub tmp 0ul 5ul) (2, 4, 2, 2, 2) /\
    F51.felem_fits h1 (gsub tmp 10ul 5ul) (2, 4, 2, 2, 2) /\
    F51.felem_fits h1 (gsub tmp 15ul 5ul) (9, 10, 9, 9, 9) /\
    F51.fevalh h1 (gsub tmp 15ul 5ul) == g /\
    F51.fevalh h1 (gsub tmp 10ul 5ul) == h /\
    F51.fevalh h1 (gsub tmp 0ul 5ul) == c))

let point_double_step_1 p tmp =
  let tmp1 = sub tmp 0ul 5ul in // c
  let tmp2 = sub tmp 5ul 5ul in
  let tmp3 = sub tmp 10ul 5ul in // h
  let tmp4 = sub tmp 15ul 5ul in // g
  let x1 = getx p in
  let y1 = gety p in
  let z1 = getz p in

  fsquare tmp1 x1;            // tmp1 = a
  fsquare tmp2 y1;            // tmp2 = b
  fsum tmp3 tmp1 tmp2;        // tmp3 = tmp1 + tmp2 = h
  fdifference tmp4 tmp1 tmp2; // tmp4 = tmp1 - tmp2 = g

  fsquare tmp1 z1;            // tmp1 = z1 * z1
  times_2 tmp1 tmp1           // tmp1 = 2 * tmp1 = c


inline_for_extraction noextract
val point_double_step_2: p:point -> tmp:lbuffer uint64 20ul -> Stack unit
  (requires fun h ->
    live h p /\ live h tmp /\ disjoint p tmp /\
    F51.point_inv_t h p /\
    F51.felem_fits h (gsub tmp 10ul 5ul) (9, 10, 9, 9, 9) /\
    F51.felem_fits h (gsub tmp 15ul 5ul) (9, 10, 9, 9, 9) /\
    F51.felem_fits h (gsub tmp 0ul 5ul) (2, 4, 2, 2, 2))
  (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
    (let x1, y1, z1, t1 = F51.point_eval h0 p in
    let c = F51.fevalh h0 (gsub tmp 0ul 5ul) in
    let h = F51.fevalh h0 (gsub tmp 10ul 5ul) in
    let g = F51.fevalh h0 (gsub tmp 15ul 5ul) in
    let e = h `SC.fsub` ((x1 `SC.fadd` y1) `SC.fmul` (x1 `SC.fadd` y1)) in
    let f = c `SC.fadd` g in
    F51.felem_fits h1 (gsub tmp 0ul 5ul) (9, 10, 9, 9, 9) /\
    F51.felem_fits h1 (gsub tmp 5ul 5ul) (9, 10, 9, 9, 9) /\
    F51.felem_fits h1 (gsub tmp 10ul 5ul) (9, 10, 9, 9, 9) /\
    F51.felem_fits h1 (gsub tmp 15ul 5ul) (9, 10, 9, 9, 9) /\
    F51.fevalh h1 (gsub tmp 0ul 5ul) == f /\
    F51.fevalh h1 (gsub tmp 5ul 5ul) == e /\
    F51.fevalh h1 (gsub tmp 10ul 5ul) == h /\
    F51.fevalh h1 (gsub tmp 15ul 5ul) == g))

let point_double_step_2 p tmp =
  let tmp1 = sub tmp 0ul 5ul in // c, f
  let tmp2 = sub tmp 5ul 5ul in // e
  let tmp3 = sub tmp 10ul 5ul in // h
  let tmp4 = sub tmp 15ul 5ul in // g
  let x1 = getx p in
  let y1 = gety p in

  fsum tmp2 x1 y1;            // tmp2 = x1 + y1
  fsquare tmp2 tmp2;          // tmp2 = (x1 + y1) ** 2
  reduce_513 tmp3;
  fdifference tmp2 tmp3 tmp2; // tmp2 = tmp3 - tmp2 = h - (x1 + y1) ** 2 = e

  reduce_513 tmp1;
  reduce_513 tmp4;
  fsum tmp1 tmp1 tmp4        // tmp1 = c + g = tmp1 + tmp4 = f


inline_for_extraction noextract
val point_double_: out:point -> p:point -> tmp:lbuffer uint64 20ul -> Stack unit
  (requires fun h ->
    live h out /\ live h p /\ live h tmp /\
    eq_or_disjoint out p /\ disjoint tmp p /\ disjoint tmp out /\
    F51.point_inv_t h p)
  (ensures fun h0 _ h1 -> modifies (loc out |+| loc tmp) h0 h1 /\
    F51.point_inv_t h1 out /\
    F51.point_eval h1 out == Spec.Ed25519.point_double (F51.point_eval h0 p))

let point_double_ out p tmp =
  point_double_step_1 p tmp;
  point_double_step_2 p tmp;
  let tmp_f = sub tmp 0ul 5ul in
  let tmp_e = sub tmp 5ul 5ul in
  let tmp_h = sub tmp 10ul 5ul in
  let tmp_g = sub tmp 15ul 5ul in
  let x3 = getx out in
  let y3 = gety out in
  let z3 = getz out in
  let t3 = gett out in
  fmul x3 tmp_e tmp_f;
  fmul y3 tmp_g tmp_h;
  fmul t3 tmp_e tmp_h;
  fmul z3 tmp_f tmp_g


val point_double: out:point -> p:point -> Stack unit
  (requires fun h ->
    live h out /\ live h p /\ eq_or_disjoint out p /\
    F51.point_inv_t h p)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\
    F51.point_eval h1 out == Spec.Ed25519.point_double (F51.point_eval h0 p))

let point_double out p =
  push_frame();
  let tmp = create 20ul (u64 0) in
  point_double_ out p tmp;
  pop_frame()
