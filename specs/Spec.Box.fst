module Spec.Box

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RawIntTypes
open Lib.LoopCombinators
open Spec.SecretBox

#set-options "--z3rlimit 100"
(* Constants *)
let size_publickey = 32 (* in bytes *)
let size_secretkey = 32   (* in bytes *)

type publickey = lbytes size_publickey
type secretkey = lbytes size_secretkey

let box_init (pk:publickey) (sk:secretkey) : key =
  let shared = Spec.Curve25519.scalarmult sk pk in
  let n = create 16 (u8 0) in
  let k = Spec.Salsa20.hsalsa20 shared n in
  k

let box_detached (sk:secretkey) (pk:publickey) (n:nonce) (m:bytes{length m / size_block <= max_size_t}) : (tag & c:bytes{length c = length m}) =
  let k = box_init pk sk in
  secretbox_detached k n m

let box_open_detached (pk:publickey) (sk:secretkey) (n:nonce) (t:tag) (c:bytes{length c / size_block <= max_size_t}) : option (m:bytes{length m = length c}) =
  let k = box_init pk sk in
  secretbox_open_detached k n t c

let box_easy (sk:secretkey) (pk:publickey) (n:nonce) (m:bytes{length m / size_block <= max_size_t}) : c:bytes{length c = size_tag + length m} =
  let (tg,c) = box_detached sk pk n m in
  Seq.append tg c

let box_open_easy (pk:secretkey) (sk:publickey) (n:nonce) (c:bytes{length c >= size_tag /\ (length c - size_tag) / size_block <= max_size_t}) : option (m:bytes{length m = length c - size_tag}) =
  let tg = Seq.slice c 0 size_tag in
  let e = Seq.slice c size_tag (length c) in
  box_open_detached pk sk n tg e

