module Spec.Curve25519

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.NatMod
open Lib.LoopCombinators
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

let decodePoint (u:serialized_point) =
  to_elem (nat_from_bytes_le u % pow2 255)

let add_and_double q nq nqp1 =
  let x_1, z_1 = q.x, q.z in
  let x_2, z_2 = nq.x, nq.z in
  let x_3, z_3 = nqp1.x, nqp1.z in
  let a  = x_2 +% z_2 in
  let b  = x_2 -% z_2 in
  let c = x_3 +% z_3 in
  let d = x_3 -% z_3 in
  let da = d *% a in
  let cb = c *% b in
  let x_3 = da +% cb in
  let z_3 = da -% cb in
  let aa = a  **% 2 in
  let bb = b  **% 2 in
  let x_3 = x_3  **% 2 in
  let z_3 = z_3  **% 2 in
  let e = aa -% bb in
  let e121665 = e *% 121665 in
  let aa_e121665 = e121665 +% aa in 
  let x_2 = aa *% bb in
  let z_2 = e *% aa_e121665 in
  let z_3 = z_3 *% x_1 in
  Proj x_2 z_2, Proj x_3 z_3

let double nq =
  let x_2, z_2 = nq.x, nq.z in
  let a  = x_2 +% z_2 in
  let b  = x_2 -% z_2 in
  let aa = a  **% 2 in
  let bb = b  **% 2 in
  let e = aa -% bb in
  let e121665 = e *% 121665 in
  let aa_e121665 = e121665 +% aa in 
  let x_2 = aa *% bb in
  let z_2 = e *% aa_e121665 in
  Proj x_2 z_2


let ith_bit (k:scalar) (i:nat{i < 256}) : uint8 =
  let (&.) = logand #U8 in
  let q = i / 8 in let r = size (i % 8) in
  (k.[q] >>. r) &. u8 1

let ladder_step (q:proj_point) (bit:uint8) (nq,nqp1) =
  if uint_to_nat bit = 1 then (
     let nqp1, nq = add_and_double q nqp1 nq in
     nq, nqp1)
  else add_and_double q nq nqp1 
  
let montgomery_ladder (init:elem) (k:scalar) : Tot proj_point =
  let q = Proj init one in
  let nq = Proj one zero in
  let nqp1 = Proj init one in
  // bit 255 is 0 and bit 254 is 1
  let nqp1,nq = add_and_double q nqp1 nq in
  // bits 253-3 depend on scalar
  let nq,nqp1 = repeati 251
    (fun i -> ladder_step q (ith_bit k (253-i))) (nq,nqp1) in
  // bits 2-0 are 0 
  let nq = double nq in
  let nq = double nq in
  let nq = double nq in
  nq  


let encodePoint (p:proj_point) : Tot serialized_point =
  let p = p.x *% (p.z   **%  (prime - 2)) in
  nat_to_bytes_le 32 (from_elem p)

let scalarmult (k:scalar) (u:serialized_point) : Tot serialized_point =
  let u = decodePoint u in
  let res = montgomery_ladder u k in
  encodePoint res

val secret_to_public: lbytes 32 -> Tot (lbytes 32)
let secret_to_public kpriv =
  let basepoint_zeros = create 32 (u8 0) in
  let basepoint = upd basepoint_zeros (32 - 1) (u8 0x09) in
  scalarmult kpriv basepoint
