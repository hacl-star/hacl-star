module Spec.Poly1305

#reset-options "--z3rlimit 60 --fuel 0 --ifuel 0"

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

let poly1305_encode_r (rb:block) : Tot felem =
  let lo = uint_from_bytes_le (sub rb 0 8) in
  let hi = uint_from_bytes_le (sub rb 8 8) in
  let mask0 = u64 0x0ffffffc0fffffff in
  let mask1 = u64 0x0ffffffc0ffffffc in
  let lo = lo &. mask0 in
  let hi = hi &. mask1 in
  assert_norm (pow2 128 < prime);
  to_felem (uint_v hi * pow2 64 + uint_v lo)

let poly1305_init (k:key) : Tot (felem & felem) =
  let r = poly1305_encode_r (slice k 0 16) in
  zero, r

let encode (len:size_nat{len <= size_block}) (b:lbytes len) : Tot felem =
  Math.Lemmas.pow2_le_compat 128 (8 * len);
  assert_norm (pow2 128 + pow2 128 < prime);
  fadd (pow2 (8 * len)) (nat_from_bytes_le b)

let poly1305_update1 (r:felem) (len:size_nat{len <= size_block}) (b:lbytes len) (acc:felem) : Tot felem =
  (encode len b `fadd` acc) `fmul` r

let poly1305_finish (k:key) (acc:felem) : Tot tag =
  let s = nat_from_bytes_le (slice k 16 32) in
  let n = (from_felem acc + s) % pow2 128 in
  nat_to_bytes_le 16 n

let poly1305_update_last (r:felem) (l:size_nat{l < 16}) (b:lbytes l) (acc:felem) =
  if l = 0 then acc else poly1305_update1 r l b acc


let poly1305_update (text:bytes) (acc:felem) (r:felem) : Tot felem =
  repeat_blocks #uint8 #felem size_block text
    (poly1305_update1 r size_block)
    (poly1305_update_last r)
  acc

let poly1305_mac (msg:bytes) (k:key) : Tot tag =
  let acc, r = poly1305_init k in
  let acc = poly1305_update msg acc r in
  poly1305_finish k acc
