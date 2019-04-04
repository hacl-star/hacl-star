module Spec.Poly1305

#reset-options "--z3rlimit 60 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

/// Constants and Types

(* Field types and parameters *)
let prime : pos =
  let p = pow2 130 - 5 in
  assert_norm (p > 0);
  p

let felem = x:nat{x < prime}
let fadd (x:felem) (y:felem) : felem = (x + y) % prime
let fmul (x:felem) (y:felem) : felem = (x * y) % prime

let to_felem (x:nat{x < prime}) : felem = x
let from_felem (x:felem) : nat = x
let zero : felem = to_felem 0

(* Poly1305 parameters *)
let size_block : size_nat = 16
let size_key   : size_nat = 32

type block = lbytes size_block
type tag   = lbytes size_block
type key   = lbytes size_key

/// Specification

let update1 (r:felem) (len:size_nat{len <= size_block}) (b:lbytes len) (acc:felem) : Tot felem =
  Math.Lemmas.pow2_le_compat 128 (8 * len);
  assert (pow2 (8 * len) <= pow2 128);
  assert_norm (pow2 128 + pow2 128 < prime);
  let n = to_felem (pow2 (8 * len) + nat_from_bytes_le b) in
  let acc = fmul (fadd n acc) r in
  acc

let poly_update1_rem (r:felem) (l:size_nat{l < 16}) (b:lbytes l) (acc:felem) =
  if l = 0 then acc else update1 r l b acc

let poly (text:bytes) (acc:felem) (r:felem) : Tot felem =
  repeat_blocks #uint8 #felem size_block text
    (update1 r size_block)
    (poly_update1_rem r)
  acc

let finish (k:key) (acc:felem) : Tot tag =
  let s = nat_from_bytes_le (slice k 16 32) in
  let n = (from_felem acc + s) % pow2 128 in
  nat_to_bytes_le 16 n

let encode_r (rb:block) : Tot felem =
  let lo = uint_from_bytes_le (sub rb 0 8) in
  let hi = uint_from_bytes_le (sub rb 8 8) in
  let mask0 = u64 0x0ffffffc0fffffff in
  let mask1 = u64 0x0ffffffc0ffffffc in
  let lo = lo &. mask0 in
  let hi = hi &. mask1 in
  assert_norm (pow2 128 < prime);
  to_felem (uint_v hi * pow2 64 + uint_v lo)

let poly1305_init (k:key) : Tot (felem & felem) =
  let r = encode_r (slice k 0 16) in
  zero, r

let poly1305 (msg:bytes) (k:key) : Tot tag =
  let acc, r = poly1305_init k in
  let acc = poly msg acc r in
  finish k acc
