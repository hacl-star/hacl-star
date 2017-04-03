module Hacl.Ed25519.PointAdd

open FStar.Buffer
open Hacl.Bignum25519
open Hacl.Ed25519.ExtPoint

#set-options "--lax"

(* Specification:

let point_add (p:ext_point) (q:ext_point) : Tot ext_point =
  let x1, y1, z1, t1 = p in
  let x2, y2, z2, t2 = q in
  let a = (y1 `fsub` x1) `fmul` (y2 `fsub` x2) in
  let b = (y1 `fadd` x1) `fmul` (y2 `fadd` x2) in
  let c = t1 `fmul` 2 `fmul` d `fmul` t2 in
  let d = z1 `fmul` 2 `fmul` z2 in
  let e = b `fsub` a in
  let f = d `fsub` c in
  let g = d `fadd` c in
  let h = b `fadd` a in
  let x3 = e `fmul` f in
  let y3 = g `fmul` h in
  let t3 = e `fmul` h in
  let z3 = f `fmul` g in
  (x3, y3, z3, t3)

*)

val point_add:
  out:point ->
  p:point ->
  q:point ->
  St unit
let point_add out p q =
  push_frame();
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) 30ul in
  let tmp1 = sub tmp 0ul 5ul in
  let tmp2 = sub tmp 5ul 5ul in
  let tmp3 = sub tmp 10ul 5ul in
  let tmp4 = sub tmp 15ul 5ul in
  let tmp5 = sub tmp 20ul 5ul in
  let tmp6 = sub tmp 25ul 5ul in
  let x1 = getx p in
  let y1 = gety p in
  let z1 = getz p in
  let t1 = gett p in
  let x2 = getx q in
  let y2 = gety q in
  let z2 = getz q in
  let t2 = gett q in
  let x3 = getx out in
  let y3 = gety out in
  let z3 = getz out in
  let t3 = gett out in

  blit x1 0ul tmp1 0ul 5ul; // tmp1 = x1
  blit x2 0ul tmp2 0ul 5ul; // tmp2 = x2
  fdifference tmp1 y1;    // tmp1 = y1 - x1
  fdifference tmp2 y2;    // tmp2 = y2 - x2
  fmul tmp3 tmp1 tmp2;    // tmp3 = a

  blit y1 0ul tmp1 0ul 5ul; // tmp1 = y1
  blit y2 0ul tmp2 0ul 5ul; // tmp2 = y2
  fsum tmp1 x1;             // tmp1 = y1 + x1
  fsum tmp2 x2;             // tmp2 = y2 + x2
  fmul tmp4 tmp1 tmp2;      // tmp4 = b

  times_2d tmp1 t1;
  fmul tmp2 tmp1 t2;        // tmp2 = c
  times_2 tmp1 z1;
  fmul tmp5 tmp1 z2;        // tmp5 = d

  blit tmp3 0ul tmp1 0ul 5ul; // tmp1 = a
  blit tmp2 0ul tmp6 0ul 5ul; // tmp6 = c
  fdifference_reduced tmp1 tmp4; // tmp1 = e
  fdifference_reduced tmp6 tmp5; // tmp6 = f
  fsum tmp5 tmp2;                // tmp5 = g
  fsum tmp4 tmp1;                // tmp4 = h

  fmul x3 tmp1 tmp6;
  fmul y3 tmp5 tmp4;
  fmul t3 tmp1 tmp4;
  fmul z3 tmp6 tmp5;

  pop_frame()
