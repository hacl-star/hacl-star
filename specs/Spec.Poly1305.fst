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

unfold type felem = x:nat{x < prime}
let zero : felem = 0
let fadd (f1:felem) (f2:felem) : felem = (f1 + f2) % prime
let fmul (f1:felem) (f2:felem) : felem = (f1 * f2) % prime

(* Poly1305 parameters *)
let size_block : size_nat = 16
let size_key   : size_nat = 32

type block = lbytes size_block
type tag   = lbytes size_block
type key   = lbytes size_key

noeq type state = {
  r: felem;
  s: felem;
  acc: felem
}

let create_st (r:felem) (s:felem) (acc:felem) : state =
  {r = r; s = s; acc = acc}

let get_r (st:state) : felem = st.r

let get_s (st:state) : felem = st.s

let get_acc (st:state) : felem = st.acc

let set_acc (st:state) (acc:felem) =
  {st with acc = acc}

/// Specification

let update1 (r:felem) (len:size_nat{len <= size_block}) (b:lbytes len) (acc:felem) : Tot felem =
  Math.Lemmas.pow2_le_compat 128 (8 * len);
  assert (pow2 (8 * len) <= pow2 128);
  assert_norm (pow2 128 < prime);
  assert_norm (pow2 128 + nat_from_bytes_le b < prime);
  let n = pow2 (8 * len) + nat_from_bytes_le b in
  let acc = (n `fadd` acc) `fmul` r in
  acc

let update_last (r:felem) (len:size_nat{len < size_block}) (b:lbytes len) (acc:felem) : Tot felem =
  if len = 0 then acc
  else update1 r len b acc

let poly (text:bytes) (st:state) : Tot state =
  let acc =
    repeat_blocks #uint8 #felem size_block text
    (update1 st.r size_block)
    (update_last st.r)
    st.acc in
  set_acc st acc

let finish (st:state) : Tot tag =
  //replace with the u128 addition
  let n = (st.acc + st.s) % pow2 128 in
  nat_to_bytes_le 16 n

let encode_r (rb:block) : Tot felem =
  let lo = uint_from_bytes_le (sub rb 0 8) in
  let hi = uint_from_bytes_le (sub rb 8 8) in
  let mask0 = u64 0x0ffffffc0fffffff in
  let mask1 = u64 0x0ffffffc0ffffffc in
  let lo = lo &. mask0 in
  let hi = hi &. mask1 in
  assert_norm (pow2 128 < prime);
  uint_v hi * pow2 64 + uint_v lo

let poly1305_init (k:key) : Tot state =
  assert_norm (pow2 128 < prime);
  let r = encode_r (sub k 0 16) in
  let s = nat_from_bytes_le (sub k 16 16) in
  {r = r; s = s; acc = zero}

let poly1305 (msg:bytes) (k:key) : Tot tag =
  let st = poly1305_init k in
  let st = poly msg st in
  finish st
