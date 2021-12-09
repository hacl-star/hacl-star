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
  let x = sub p 0ul 5ul in
  let y = sub p 5ul 5ul in
  let z = sub p 10ul 5ul in
  let t = sub p 15ul 5ul in

  let x1 = sub out 0ul 5ul in
  let y1 = sub out 5ul 5ul in
  let z1 = sub out 10ul 5ul in
  let t1 = sub out 15ul 5ul in

  copy x1 x;
  fdifference x1 zero;
  reduce_513 x1;
  copy y1 y;
  copy z1 z;
  copy t1 t;
  fdifference t1 zero;
  reduce_513 t1;
  pop_frame ()
