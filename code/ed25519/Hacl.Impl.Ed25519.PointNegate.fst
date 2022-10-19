module Hacl.Impl.Ed25519.PointNegate

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

module F51 = Hacl.Impl.Ed25519.Field51
module SC = Spec.Curve25519

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val point_negate: p:F51.point -> out:F51.point ->
  Stack unit
  (requires fun h ->
    live h out /\ live h p /\ disjoint out p /\
    F51.point_inv_t h p)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
   (let (x1, y1, z1, t1) = F51.point_eval h0 p in
    F51.point_inv_t h1 out /\
    F51.point_eval h1 out == SC.((-x1) % prime, y1, z1, (-t1) % prime)))

let point_negate p out =
  push_frame ();
  let zero = create 5ul (u64 0) in
  make_zero zero;
  let x = getx p in
  let y = gety p in
  let z = getz p in
  let t = gett p in

  let x1 = getx out in
  let y1 = gety out in
  let z1 = getz out in
  let t1 = gett out in

  fdifference x1 zero x;
  reduce_513 x1;
  copy y1 y;
  copy z1 z;
  fdifference t1 zero t;
  reduce_513 t1;
  pop_frame ()
