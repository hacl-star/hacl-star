module Spec.Poly1305

#reset-options "--z3rlimit 60 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Poly1305.Lemmas

(* Field types and parameters *)
let prime =  pow2 130 - 5
type elem = e:nat{e >= 0 /\ e < prime}
let fadd (e1:elem) (e2:elem) = (e1 + e2) % prime
let fmul (e1:elem) (e2:elem) = (e1 * e2) % prime
let zero : elem = 0
let one  : elem = 1

(* Poly1305 parameters *)
let blocksize : size_nat = 16
let keysize   : size_nat = 32
type block = lbytes blocksize
type tag   = lbytes blocksize
type key   = lbytes keysize


type state = {
  r:elem;
  s:elem;
  acc:elem
}

let set_acc (st:state) (acc:elem) =
  {st with acc = acc}

(* Poly1305 specification *)
let update1 (len:size_nat{len <= blocksize}) (b:lbytes len) (st:state) : state =
  Math.Lemmas.pow2_le_compat 128 (8 * len);
  assert (pow2 (8 * len) <= pow2 128);
  let n = pow2 (8 * len) `fadd` nat_from_bytes_le b in
  set_acc st ((n `fadd` st.acc) `fmul` st.r)


let update_blocks (n:size_nat{n * blocksize <= max_size_t}) (text:lbytes (n * blocksize)) (st:state) : state =
  repeati n (fun i st ->
    let b = slice text (blocksize * i) (blocksize * (i+1)) in
    update1 16 b st) st

let poly (len:size_nat) (text:lbytes len) (st:state) : state =
  let n = len / blocksize in
  let rem = len % blocksize in
  let blocks = slice text 0 (n * blocksize) in
  let st = update_blocks n blocks st in
  if rem = 0 then st
  else
    let last = slice text (n * blocksize) len in
    update1 rem last st

let finish (st:state) : tag =
  let n = (st.acc + st.s) % pow2 128 in
  nat_to_bytes_le 16 n

let encode_r (rb:block) : elem =
  let rb = rb.[3] <- rb.[3] &. u8 15 in
  let rb = rb.[7] <- rb.[7] &. u8 15 in
  let rb = rb.[11] <- rb.[11] &. u8 15 in
  let rb = rb.[15] <- rb.[15] &. u8 15 in
  let rb = rb.[4] <- rb.[4] &. u8 252 in
  let rb = rb.[8] <- rb.[8] &. u8 252 in
  let rb = rb.[12] <- rb.[12] &. u8 252 in
  nat_from_bytes_le rb

let poly1305_init (k:key) : state =
  let r = encode_r (slice k 0 16) in
  let s = nat_from_bytes_le (slice k 16 32) in
  {r = r; s = s; acc = 0}

let poly1305 (len:size_nat) (msg:lbytes len) (k:key) : tag =
  let st = poly1305_init k in
  let st = poly len msg st in
  finish st
