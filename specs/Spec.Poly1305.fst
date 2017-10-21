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

let blocksize : size_t = 16
let keysize   : size_t = 32

type block = lbytes blocksize
type tag   = lbytes blocksize
type key   = lbytes keysize

(* Specification code *)
let update_block (b:block) (r:elem) (acc:elem) : elem =
  let n = pow2 128 `fadd` nat_from_bytes_le b  in
  (n `fadd` acc) `fmul` r

let update_last (len:size_t{len < blocksize}) (b:lbytes len) 
		(r:elem) (acc:elem) : elem =
  assert (pow2 (8 * len) < pow2 128);
  let n = pow2 (8 * len) `fadd` nat_from_bytes_le b in
  (n `fadd` acc) `fmul` r

let poly (len:size_t) (text:lbytes len) (r:elem) : elem =
  let blocks = len / blocksize in
  let rem = len % blocksize in
  let init  : elem = 0 in
  let acc   : elem = 
    repeati blocks
      (fun i acc  -> let b = slice text (blocksize * i) (blocksize * (i+1)) in
	          update_block b r acc) 
      init in
  if rem = 0 then
     acc
  else 
     let last = slice text (blocks * blocksize) len in
     update_last rem last r acc
  
let finish (a:elem) (s:elem) : tag =
  let n = (a + s) % pow2 128 in
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

let poly1305 (len:size_t) (msg:lbytes len) (k:key) : tag =
  let r = encode_r (slice k 0 16) in
  let s = nat_from_bytes_le (slice k 16 32) in
  finish (poly len msg r) s


