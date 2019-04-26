module Spec.Curve25519

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Curve25519.Lemmas

(* Field types and parameters *)
let prime : pos = pow2 255 - 19

type elem = x:nat{x < prime}
let zero : elem = 0
let one  : elem = 1

let fadd (x:elem) (y:elem) : elem = (x + y) % prime
let fsub (x:elem) (y:elem) : elem = (x - y) % prime
let fmul (x:elem) (y:elem) : elem = (x * y) % prime

let ( +% ) = fadd
let ( -% ) = fsub
let ( *% ) = fmul

val fpow: a:elem -> b:pos -> Tot (res:elem) (decreases b)
let rec fpow a b =
  if b = 1 then a
  else
    if b % 2 = 0 then fpow (a *% a) (b / 2)
    else a *% (fpow (a *% a) (b / 2))

let ( **% ) = fpow

(* Type aliases *)
type scalar = lbytes 32
type serialized_point = lbytes 32
type proj_point = elem & elem

let ith_bit (k:scalar) (i:nat{i < 256}) : uint64 =
  let q = i / 8 in let r = size (i % 8) in
  to_u64 ((k.[q] >>. r) &. u8 1)

let decodePoint (u:serialized_point) =
  (nat_from_bytes_le u % pow2 255) % prime

let encodePoint (p:proj_point) : Tot serialized_point =
  let x, z = p in
  let p = x *% (z **% (prime - 2)) in
  nat_to_bytes_le 32 p

let add_and_double q nq nqp1 =
  let x_1, z_1 = q in
  let x_2, z_2 = nq in
  let x_3, z_3 = nqp1 in
  let a = x_2 +% z_2 in
  let b = x_2 -% z_2 in
  let c = x_3 +% z_3 in
  let d = x_3 -% z_3 in
  let da = d *% a in
  let cb = c *% b in
  let x_3 = da +% cb in
  let z_3 = da -% cb in
  let aa = a *% a in
  let bb = b *% b in
  let x_3 = x_3 *% x_3 in
  let z_3 = z_3 *% z_3 in
  let e = aa -% bb in
  let e121665 = e *% 121665 in
  let aa_e121665 = e121665 +% aa in
  let x_2 = aa *% bb in
  let z_2 = e *% aa_e121665 in
  let z_3 = z_3 *% x_1 in
  (x_2, z_2), (x_3, z_3)

let double nq =
  let x_2, z_2 = nq in
  let a = x_2 +% z_2 in
  let b = x_2 -% z_2 in
  let aa = a *% a in
  let bb = b *% b in
  let e = aa -% bb in
  let e121665 = e *% 121665 in
  let aa_e121665 = e121665 +% aa in
  let x_2 = aa *% bb in
  let z_2 = e *% aa_e121665 in
  x_2, z_2

let cswap2 (sw:uint64) (nq:proj_point) (nqp1:proj_point) =
  let open Lib.RawIntTypes in
  if uint_to_nat sw = 1 then (nqp1, nq) else (nq, nqp1)

let ladder_step (k:scalar) (q:proj_point) (i:nat{i < 251}) (nq, nqp1, swap) =
  let bit = ith_bit k (253-i) in
  let sw = swap ^. bit in
  let nq, nqp1 = cswap2 sw nq nqp1 in
  let nq, nqp1 = add_and_double q nq nqp1 in
  (nq, nqp1, bit)

let montgomery_ladder (init:elem) (k:scalar) : Tot proj_point =
  let q = (init, one) in
  let nq = (one, zero) in
  let nqp1 = (init, one) in
  // bit 255 is 0 and bit 254 is 1
  let nq,nqp1 = cswap2 (u64 1) nq nqp1 in
  let nq,nqp1 = add_and_double q nq nqp1 in
  let swap = u64 1 in
  // bits 253-3 depend on scalar
  let nq,nqp1,swap = Lib.LoopCombinators.repeati 251 (ladder_step k q) (nq, nqp1, swap) in
  let nq,nqp1 = cswap2 swap nq nqp1 in
  // bits 2-0 are 0
  let nq = double nq in
  let nq = double nq in
  let nq = double nq in
  nq

let scalarmult (k:scalar) (u:serialized_point) : Tot serialized_point =
  let u = decodePoint u in
  let res = montgomery_ladder u k in
  encodePoint res

inline_for_extraction
let basepoint_list : x:list byte_t{List.Tot.length x == 32} =
  [@inline_let]
  let l =
    [9uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy] in
  assert_norm (List.Tot.length l == 32);
  l

let basepoint_lseq : Lib.Sequence.lseq byte_t 32 =
  Lib.Sequence.of_list basepoint_list

val secret_to_public: lbytes 32 -> lbytes 32
let secret_to_public kpriv =
  let basepoint = map secret basepoint_lseq in
  scalarmult kpriv basepoint
