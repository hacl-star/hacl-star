module Hacl.Impl.Ed25519.PointDouble

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

inline_for_extraction noextract
val point_double_step_1:
    p:point
  -> tmp:lbuffer uint64 30ul ->
  Stack unit
    (requires fun h -> live h p /\ live h tmp /\ disjoint p tmp)
    (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1)
let point_double_step_1 p tmp =
  let tmp1 = sub tmp 0ul 5ul in
  let tmp2 = sub tmp 5ul 5ul in
  let tmp3 = sub tmp 10ul 5ul in
  let tmp4 = sub tmp 15ul 5ul in
  let tmp5 = sub tmp 20ul 5ul in
  let tmp6 = sub tmp 25ul 5ul in
  let x1 = getx p in
  let y1 = gety p in
  let z1 = getz p in
  fsquare tmp1 x1; // tmp1 = a
  fsquare tmp2 y1; // tmp2 = b
  fsquare tmp3 z1;
  times_2 tmp4 tmp3; // tmp4 = c
  copy tmp3 tmp1; // tmp3 = a
  fsum tmp3 tmp2; // tmp3 = h
  reduce_513 tmp3

inline_for_extraction noextract
val point_double_step_2:
    p:point
  -> tmp:lbuffer uint64 30ul ->
  Stack unit
    (requires fun h -> live h p /\ live h tmp /\ disjoint p tmp)
    (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1)
let point_double_step_2 p tmp =
  let tmp1 = sub tmp 0ul 5ul in
  let tmp2 = sub tmp 5ul 5ul in
  let tmp3 = sub tmp 10ul 5ul in
  let tmp4 = sub tmp 15ul 5ul in
  let tmp5 = sub tmp 20ul 5ul in
  let tmp6 = sub tmp 25ul 5ul in
  let x1 = getx p in
  let y1 = gety p in
  copy tmp5 x1; // tmp5 = x1
  fsum tmp5 y1;             // tmp5 = x1 + y1
  fsquare tmp6 tmp5;        // tmp6 = (x1 + y1) ** 2
  copy tmp5 tmp3; // tmp5 = h
  fdifference tmp6 tmp5;      // tmp6 = e
  fdifference_reduced tmp2 tmp1;      // tmp2 = g
  reduce_513 tmp4;
  fsum tmp4 tmp2             // tmp4 = f

inline_for_extraction noextract
val point_double_:
    out:point
  -> p:point
  -> tmp:lbuffer uint64 30ul ->
  Stack unit
    (requires fun h ->
      live h out /\ live h p /\ live h tmp /\
      disjoint out p /\ disjoint tmp p /\ disjoint tmp out)
    (ensures fun h0 _ h1 -> modifies (loc out |+| loc tmp) h0 h1)
let point_double_ out p tmp =
  let tmp1 = sub tmp 0ul 5ul in
  let tmp2 = sub tmp 5ul 5ul in
  let tmp3 = sub tmp 10ul 5ul in
  let tmp4 = sub tmp 15ul 5ul in
  let tmp5 = sub tmp 20ul 5ul in
  let tmp6 = sub tmp 25ul 5ul in
  let x3 = getx out in
  let y3 = gety out in
  let z3 = getz out in
  let t3 = gett out in
  point_double_step_1 p tmp;
  point_double_step_2 p tmp;
  fmul x3 tmp4 tmp6;
  fmul y3 tmp2 tmp3;
  fmul t3 tmp3 tmp6;
  fmul z3 tmp4 tmp2

val point_double:
    out:point
  -> p:point ->
  Stack unit
    (requires fun h -> live h out /\ live h p /\ disjoint out p)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1)
let point_double out p =
  push_frame();
  let tmp = create 30ul (u64 0) in
  point_double_ out p tmp;
  pop_frame()
