module Hacl.Impl.Ed25519.PointDouble

open FStar.Buffer
open Hacl.Bignum25519
open Hacl.Impl.Ed25519.ExtPoint

#set-options "--lax"

(* Specification 

let point_double (p:ext_point) : Tot ext_point =
  let x1, y1, z1, t1 = p in
  let a = x1 ** 2 in
  let b = y1 ** 2 in
  let c = 2 `fmul` (z1 ** 2) in
  let h = a `fadd` b in
  let e = h `fsub` ((x1 `fadd` y1) ** 2) in
  let g = a `fsub` b in
  let f = c `fadd` g in
  let x3 = e `fmul` f in
  let y3 = g `fmul` h in
  let t3 = e `fmul` h in
  let z3 = f `fmul` g in
  (x3, y3, z3, t3)

*)

val point_double:
  out:point ->
  p:point ->
  St unit
let point_double out p =
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
  let x3 = getx out in
  let y3 = gety out in
  let z3 = getz out in
  let t3 = gett out in

  fsquare tmp1 x1; // tmp1 = a
  fsquare tmp2 y1; // tmp2 = b
  fsquare tmp3 z1;
  times_2 tmp4 tmp3; // tmp4 = c

  blit tmp1 0ul tmp3 0ul 5ul; // tmp3 = a
  fsum tmp3 tmp2; // tmp3 = h

  blit x1 0ul tmp5 0ul 5ul; // tmp5 = x1
  fsum tmp5 y1;             // tmp5 = x1 + y1
  fsquare tmp6 tmp5;        // tmp6 = (x1 + y1) ** 2
  blit tmp3 0ul tmp5 0ul 5ul; // tmp5 = h
  fsum tmp5 tmp6;             // tmp5 = e
  fsum tmp1 tmp2;             // tmp1 = g
  fsum tmp4 tmp1;             // tmp4 = f
  fmul x3 tmp5 tmp4;
  fmul y3 tmp1 tmp3;
  fmul t3 tmp5 tmp3;
  fmul z3 tmp4 tmp1;

  pop_frame()
