module Spec.Poly

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

(** https://tools.ietf.org/html/rfc7539#page-13 *)

(* Field types and parameters *)
let prime : pos =
  let p = pow2 130 - 5 in
  assert_norm (p > 0);
  p

let felem = x:nat{x < prime}
let zero : felem = 0
let to_felem (x:nat{x < prime}) : felem = x
let from_felem (x:felem) : nat = x

let fadd (x:felem) (y:felem) : felem = (x + y) % prime
let fmul (x:felem) (y:felem) : felem = (x * y) % prime

(* Poly1305 parameters *)
let blocksize : size_nat = 16
let block = lbytes blocksize

let encode_block (b:lbytes blocksize) : Tot felem =
  (**) assert_norm (pow2 128 + pow2 128 < prime);
  to_felem (pow2 128 + nat_from_bytes_le b)

(* Polynomial evaluation *)
let poly1305_update1 (r:felem) (b:lbytes blocksize) (acc:felem) : Tot felem =
  (encode_block b `fadd` acc) `fmul` r

let poly1305_update1_f (msg:bytes) (r:felem) (i:nat{i < length msg / blocksize}) (acc:felem) : Tot felem =
  (**) Math.Lemmas.lemma_mult_le_right blocksize (i + 1) (length msg / blocksize);
  (**) Math.Lemmas.multiply_fractions (length msg) blocksize;
  let block = Seq.slice msg (i * blocksize) (i * blocksize + blocksize) in
  poly1305_update1 r block acc

let poly1305_update_multi (msg:bytes{length msg % blocksize = 0}) (r:felem) (acc:felem) : Tot felem =
  let nb = length msg / blocksize in
  Lib.LoopCombinators.repeati nb (poly1305_update1_f msg r) acc

//or: repeat_blocks_multi blocksize msg (poly1305_update1 r) acc
