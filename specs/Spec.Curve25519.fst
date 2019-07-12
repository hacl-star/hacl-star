module Spec.Curve25519

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.NatMod

open Spec.Curve25519.Lemmas


#reset-options "--max_fuel 0 --z3rlimit 20"

(* Field types and parameters *)
let prime = pow2 255 - 19

unfold type elem = nat_mod prime
let to_elem x = x `modulo` prime
let from_elem (x:elem) = nat_mod_v x
let zero : elem = to_elem 0
let one  : elem = to_elem 1

(* Type aliases *)
type scalar = lbytes 32
type serialized_point = lbytes 32
noeq type proj_point = | Proj: x:elem -> z:elem -> proj_point

let decodeScalar25519 (k:scalar) =
  let (&.) = logand #U8 in
  let k :scalar = k.[0] <- (k.[0] &. u8 248)          in
  let k :scalar = k.[31] <- ((k.[31] &. u8 127) |. u8 64) in k

let decodePoint (u:serialized_point) =
  to_elem (nat_from_bytes_le u % pow2 255)

let add_and_double qx nq nqp1 =
  let x_1 = qx in
  let x_2, z_2 = nq.x, nq.z in
  let x_3, z_3 = nqp1.x, nqp1.z in
  let a  = x_2 +% z_2 in
  let aa = a  **% 2 in
  let b  = x_2 -% z_2 in
  let bb = b  **% 2 in
  let e = aa -% bb in
  let c = x_3 +% z_3 in
  let d = x_3 -% z_3 in
  let da = d *% a in
  let cb = c *% b in
  let x_3 = (da +% cb)  **% 2 in
  let z_3 = x_1 *% ((da -% cb)  **% 2) in
  let x_2 = aa *% bb in
  let z_2 = e *% (aa +% (to_elem 121665 *% e)) in
  Proj x_2 z_2, Proj x_3 z_3

let ith_bit (k:scalar) (i:nat{i < 256}) : uint8 =
  let (&.) = logand #U8 in
  let q = i / 8 in let r = size (i % 8) in
  (k.[q] >>. r) &. u8 1

let rec montgomery_ladder_ (init:elem) x xp1 (k:scalar) (ctr:nat{ctr<=256})
  : Tot proj_point (decreases ctr) =
  if ctr = 0 then x
  else (
    let ctr' = ctr - 1 in
    let (x', xp1') =
      if uint_to_nat #U8 (ith_bit k ctr') = 1 then (
        let nqp2, nqp1 = add_and_double init xp1 x in
        nqp1, nqp2
      ) else add_and_double init x xp1 in
    montgomery_ladder_ init x' xp1' k ctr'
  )

let montgomery_ladder (init:elem) (k:scalar) : Tot proj_point =
  montgomery_ladder_ init (Proj one zero) (Proj init one) k 256

let encodePoint (p:proj_point) : Tot serialized_point =
  let p = p.x *% (p.z   **%  (prime - 2)) in
  nat_to_bytes_le 32 (from_elem p)

let scalarmult (k:scalar) (u:serialized_point) : Tot serialized_point =
  let k = decodeScalar25519 k in
  let u = decodePoint u in
  let res = montgomery_ladder u k in
  encodePoint res

let scalarmult' (k:scalar) (u:serialized_point) : Tot serialized_point =
  let u = decodePoint u in
  let res = montgomery_ladder u k in
  encodePoint res

val secret_to_public: lbytes 32 -> Tot (lbytes 32)
let secret_to_public kpriv =
  let basepoint_zeros = create 32 (u8 0) in
  let basepoint = upd basepoint_zeros (32 - 1) (u8 0x09) in
  scalarmult kpriv basepoint
