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

let get_r (st:state) : felem = st.r

let get_s (st:state) : felem = st.s

let get_acc (st:state) : felem = st.acc

let create_st (r:felem) (s:felem) (acc:felem) : state =
  {r = r; s = s; acc = acc}

/// Specification

let set_acc (st:state) (acc:felem) =
  {st with acc = acc}

let update1 (len:size_nat{len <= size_block}) (b:lbytes len) (st:state) : Tot state =
  Math.Lemmas.pow2_le_compat 128 (8 * len);
  assert (pow2 (8 * len) <= pow2 128);
  assert_norm (pow2 128 < prime);
  assert_norm (pow2 128 + nat_from_bytes_le b < prime);
  let n = pow2 (8 * len) + nat_from_bytes_le b in
  let acc = (n `fadd` st.acc) `fmul` st.r in
  set_acc st acc

let poly (text:bytes) (st:state) : Tot state =
  repeat_blocks #uint8 #state size_block text
    (fun b -> update1 size_block b)
    (fun l b a -> if l = 0 then a else update1 l b a)
  st

let finish (st:state) : Tot tag =
  let n = (st.acc + st.s) % pow2 128 in
  nat_to_bytes_le 16 n

let encode_r (rb:block) : Tot felem =
  let (&.) = logand #U8 in
  let rb = rb.[3] <- rb.[3] &. u8 15 in
  let rb = rb.[7] <- rb.[7] &. u8 15 in
  let rb = rb.[11] <- rb.[11] &. u8 15 in
  let rb = rb.[15] <- rb.[15] &. u8 15 in
  let rb = rb.[4] <- rb.[4] &. u8 252 in
  let rb : lseq uint8 16 = rb.[8] <- rb.[8] &. u8 252 in
  let rb : lseq uint8 16 = rb.[12] <- rb.[12] &. u8 252 in
  assert_norm (pow2 128 < prime);
  nat_from_bytes_le rb

let poly1305_init (k:key) : Tot state =
  assert_norm (pow2 128 < prime);
  let r = encode_r (sub k 0 16) in
  let s = nat_from_bytes_le (sub k 16 16) in
  {r = r; s = s; acc = zero}

let poly1305 (msg:bytes) (k:key) : Tot tag =
  let st = poly1305_init k in
  let st = poly msg st in
  finish st
