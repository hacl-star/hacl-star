module Hacl.Impl.Ed25519.PointAdd

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

inline_for_extraction noextract
val point_add_step_1:
    p:point
  -> q:point
  -> tmp:lbuffer uint64 30ul ->
  Stack unit
    (requires fun h ->
      live h p /\ live h q /\ live h tmp /\
      disjoint tmp p /\ disjoint tmp q)
    (ensures fun h0 _ h1 -> modifies (loc tmp) h0 h1)
let point_add_step_1 p q tmp =
  let tmp1 = sub tmp 0ul 5ul in
  let tmp2 = sub tmp 5ul 5ul in
  let tmp3 = sub tmp 10ul 5ul in
  let tmp4 = sub tmp 15ul 5ul in
  //let tmp5 = sub tmp 20ul 5ul in
  //let tmp6 = sub tmp 25ul 5ul in
  let x1 = getx p in
  let y1 = gety p in
  let x2 = getx q in
  let y2 = gety q in
  copy tmp1 x1; // tmp1 = x1
  copy tmp2 x2; // tmp2 = x2
  fdifference_reduced tmp1 y1;    // tmp1 = y1 - x1
  fdifference tmp2 y2;    // tmp2 = y2 - x2
  fmul tmp3 tmp1 tmp2;    // tmp3 = a
  copy tmp1 y1; // tmp1 = y1
  copy tmp2 y2; // tmp2 = y2
  fsum tmp1 x1;             // tmp1 = y1 + x1
  fsum tmp2 x2;             // tmp2 = y2 + x2
  fmul tmp4 tmp1 tmp2

inline_for_extraction noextract
val point_add_step_2:
    p:point
  -> q:point
  -> tmp:lbuffer uint64 30ul ->
  Stack unit
    (requires fun h ->
      live h p /\ live h q /\ live h tmp /\
      disjoint tmp p /\ disjoint tmp q)
    (ensures fun h0 _ h1 -> modifies (loc tmp) h0 h1)
let point_add_step_2 p q tmp =
  let tmp1 = sub tmp 0ul 5ul in
  let tmp2 = sub tmp 5ul 5ul in
  let tmp3 = sub tmp 10ul 5ul in
  let tmp4 = sub tmp 15ul 5ul in
  let tmp5 = sub tmp 20ul 5ul in
  let tmp6 = sub tmp 25ul 5ul in
  let z1 = getz p in
  let t1 = gett p in
  let z2 = getz q in
  let t2 = gett q in
  times_2d tmp1 t1;
  fmul tmp2 tmp1 t2;        // tmp2 = c
  times_2 tmp1 z1;
  fmul tmp5 tmp1 z2;        // tmp5 = d
  copy tmp1 tmp3; // tmp1 = a
  copy tmp6 tmp2; // tmp6 = c
  fdifference_reduced tmp1 tmp4; // tmp1 = e
  fdifference tmp6 tmp5; // tmp6 = f
  fsum tmp5 tmp2;                // tmp5 = g
  fsum tmp4 tmp3                // tmp4 = h

inline_for_extraction noextract
val point_add_:
    out:point
  -> p:point
  -> q:point
  -> tmp:lbuffer uint64 30ul ->
  Stack unit
    (requires fun h ->
      live h out /\ live h p /\ live h q /\ live h tmp /\
      disjoint tmp p /\ disjoint tmp q /\ disjoint tmp out /\
      disjoint p out /\ disjoint q out)
    (ensures fun h0 _ h1 -> modifies (loc out |+| loc tmp) h0 h1)
let point_add_ out p q tmp =
  point_add_step_1 p q tmp;
  point_add_step_2 p q tmp;
  let tmp1 = sub tmp 0ul 5ul in
  //let tmp2 = sub tmp 5ul 5ul in
  //let tmp3 = sub tmp 10ul 5ul in
  let tmp4 = sub tmp 15ul 5ul in
  let tmp5 = sub tmp 20ul 5ul in
  let tmp6 = sub tmp 25ul 5ul in
  let x3 = getx out in
  let y3 = gety out in
  let z3 = getz out in
  let t3 = gett out in
  fmul x3 tmp1 tmp6;
  fmul y3 tmp5 tmp4;
  fmul t3 tmp1 tmp4;
  fmul z3 tmp5 tmp6

val point_add:
    out:point
  -> p:point
  -> q:point ->
  Stack unit
    (requires fun h ->
      live h out /\ live h p /\ live h q /\
      disjoint p out /\ disjoint q out)
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1)
let point_add out p q =
  push_frame();
  let tmp = create 30ul (u64 0) in
  point_add_ out p q tmp;
  pop_frame()
