module Spec.P256

open FStar.Mul

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence

open Spec.P256.Definitions
open Spec.P256.Lemmas

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(*
Curve NIST-P256

y^2 = x^3-3x+41058363725152142129326129780047268409114441015993725554835256314039467401291

modulo p = 2^256 - 2^224 + 2^192 + 2^96 - 1 *)

let prime = prime256

let aCoordinateP256 = -3 
let bCoordinateP256 : (a: nat {a < prime256}) =
  assert_norm (41058363725152142129326129780047268409114441015993725554835256314039467401291 < prime256);
  41058363725152142129326129780047268409114441015993725554835256314039467401291

noextract
let basePoint : point_nat_prime =
  assert_norm (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296 < prime256);
  (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
   0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5,
   1)


noextract
let _point_double (p:point_nat_prime) : point_nat_prime =
  let x, y, z = p in
  let s = (4 * x * y * y) % prime256 in
  let m = ((-3) * z * z * z * z + 3 * x * x) % prime256 in
  let x3 = (m * m - 2 * s) % prime256 in
  let y3 = (m * (s - x3) - 8 * y * y * y * y) % prime256 in
  let z3 = (2 * y * z) % prime256 in
  (x3, y3, z3)


noextract
let _point_add (p:point_nat_prime) (q:point_nat_prime) : point_nat_prime =
  let open FStar.Tactics in
  let open FStar.Tactics.Canon in

  let (x1, y1, z1) = p in
  let (x2, y2, z2) = q in

  let z2z2 = z2 * z2 in
  let z1z1 = z1 * z1 in

  let u1 = x1 * z2z2 % prime256 in
  let u2 = x2 * z1z1 % prime256 in

  assert_by_tactic (x1 * z2 * z2 = x1 * (z2 * z2)) canon;
  assert_by_tactic (x2 * z1 * z1 = x2 * (z1 * z1)) canon;

  let s1 = y1 * z2 * z2z2 % prime256 in
  let s2 = y2 * z1 * z1z1 % prime256 in

  assert_by_tactic (y1 * z2 * (z2 * z2) = y1 * z2 * z2 * z2) canon;
  assert_by_tactic (y2 * z1 * (z1 * z1) = y2 * z1 * z1 * z1) canon;

  let h = (u2 - u1) % prime256 in
  let r = (s2 - s1) % prime256 in

  let rr = (r * r) in
  let hh = (h * h) in
  let hhh = (h * h * h) in

  assert_by_tactic (forall (n: nat). n * h * h = n * (h * h)) canon;
  assert_by_tactic (s1 * (h * h * h) = s1 * h * h * h) canon;
  let x3 = (rr - hhh - 2 * u1 * hh) % prime256 in
  assert(x3 = (r * r - h * h * h - 2 * u1 * h * h) % prime256);
  let y3 = (r * (u1 * hh - x3) - s1 * hhh) % prime256 in
  assert(y3 = (r * (u1 * h*h - x3) - s1 * h*h*h) % prime256);
  let z3 = (h * z1 * z2) % prime256 in
  if z2 = 0 then
    (x1, y1, z1)
  else
    if z1 = 0 then
      (x2, y2, z2)
    else
      (x3, y3, z3)


let isPointAtInfinity (p:point_nat) =
  let (_, _, z) = p in z = 0


let _norm (p:point_nat_prime) : point_nat_prime =
  assert_norm (prime256 - 2 > 0);
  let (x, y, z) = p in
  let z2 = z * z in
  let z2i = modp_inv2_pow z2 in
  let z3 = z * z * z in
  let z3i = modp_inv2_pow z3 in
  let x3 = (z2i * x) % prime256 in
  let y3 = (z3i * y) % prime256 in
  let z3 = if isPointAtInfinity p then 0 else 1 in
  assert(x3 == (x * (pow (z * z) (prime256 - 2) % prime256) % prime256));
  assert(y3 == (y * (pow (z * z * z) (prime256 - 2) % prime256) % prime256));
  (x3, y3, z3)


let scalar = lbytes 32


let ith_bit (k:lbytes 32) (i:nat{i < 256}) : uint64 =
  let q = 31 - i / 8 in let r = size (i % 8) in
  to_u64 ((index k q >>. r) &. u8 1)


val _ml_step0: p:point_nat_prime -> q:point_nat_prime -> tuple2 point_nat_prime point_nat_prime

let _ml_step0 r0 r1 =
  let r0 = _point_add r1 r0 in
  let r1 = _point_double r1 in
  (r0, r1)


val _ml_step1: p: point_nat_prime -> q: point_nat_prime -> tuple2 point_nat_prime point_nat_prime

let _ml_step1 r0 r1 =
  let r1 = _point_add r0 r1 in
  let r0 = _point_double r0 in
  (r0, r1)


val _ml_step: k:scalar -> i:nat{i < 256} -> tuple2 point_nat_prime point_nat_prime
  -> tuple2 point_nat_prime point_nat_prime

let _ml_step k i (p, q) =
  let bit = 255 - i in
  let bit = ith_bit k bit in
  let open Lib.RawIntTypes in
  if uint_to_nat bit = 0 then
    _ml_step1 p q
  else
    _ml_step0 p q


val montgomery_ladder_spec: k:scalar -> tuple2 point_nat_prime point_nat_prime
  -> tuple2 point_nat_prime point_nat_prime
let montgomery_ladder_spec k pq =
  Lib.LoopCombinators.repeati 256 (_ml_step k) pq


val scalar_multiplication: scalar -> point_nat_prime -> point_nat_prime
let scalar_multiplication k p =
  let pai = (0, 0, 0) in
  let q, f = montgomery_ladder_spec k (pai, p) in
  _norm q


val secret_to_public: scalar -> point_nat_prime
let secret_to_public k =
  let pai = (0, 0, 0) in
  let q, f = montgomery_ladder_spec k (pai, basePoint) in
  _norm q


val isPointOnCurve: point_nat_prime -> bool
let isPointOnCurve p =
  let (x, y, z) = p in
  (y * y) % prime =
  (x * x * x + aCoordinateP256 * x + bCoordinateP256) % prime


let point_prime_to_coordinates (p:point_seq) =
  felem_seq_as_nat (Lib.Sequence.sub p 0 4),
  felem_seq_as_nat (Lib.Sequence.sub p 4 4),
  felem_seq_as_nat (Lib.Sequence.sub p 8 4)


val toJacobianCoordinates: tuple2 nat nat -> tuple3 nat nat nat
let toJacobianCoordinates (r0, r1) = (r0, r1, 1)
