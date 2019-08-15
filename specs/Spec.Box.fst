module Spec.Box

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.SecretBox

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

(* Constants *)
let size_publickey = 32 (* in bytes *)
let size_secretkey = 32 (* in bytes *)

type publickey = lbytes size_publickey
type secretkey = lbytes size_secretkey


let ecdh (pk:publickey) (sk:secretkey) : option secretkey =
  let shared = Spec.Curve25519.scalarmult sk pk in
  if not (lbytes_eq shared (create 32 (u8 0))) then
    Some shared
  else None


let box_beforenm (pk:publickey) (sk:secretkey) : option key =
  let shared = ecdh pk sk in
  match shared with
  | Some shared -> Some (Spec.Salsa20.hsalsa20 shared (create 16 (u8 0)))
  | None -> None


let box_detached_afternm (k:key) (n:nonce) (m:bytes{length m / size_block <= max_size_t}) : tag & c:bytes{length c = length m} =
  secretbox_detached k n m


let box_detached (sk:secretkey) (pk:publickey) (n:nonce) (m:bytes{length m / size_block <= max_size_t}) : option (tag & c:bytes{length c = length m}) =
  let k = box_beforenm pk sk in
  match k with
  | Some k -> Some (box_detached_afternm k n m)
  | None -> None


let box_open_detached_afternm (k:key) (n:nonce) (t:tag) (c:bytes{length c / size_block <= max_size_t}) : option (m:bytes{length m = length c}) =
  secretbox_open_detached k n t c


let box_open_detached (pk:publickey) (sk:secretkey) (n:nonce) (t:tag) (c:bytes{length c / size_block <= max_size_t}) : option (m:bytes{length m = length c}) =
  let k = box_beforenm pk sk in
  match k with
  | Some k -> box_open_detached_afternm k n t c
  | None -> None


let box_easy_afternm (k:key) (n:nonce) (m:bytes{length m / size_block <= max_size_t}) : c:bytes{length c = size_tag + length m} =
  let (tg, c) = box_detached_afternm k n m in
  Seq.append tg c


let box_easy (sk:secretkey) (pk:publickey) (n:nonce) (m:bytes{length m / size_block <= max_size_t}) : option (c:bytes{length c = size_tag + length m}) =
  let r = box_detached sk pk n m in
  match r with
  | Some (tg, c) -> Some (Seq.append tg c)
  | None -> None


let box_open_easy_afternm (k:key) (n:nonce) (c:bytes{length c >= size_tag /\ (length c - size_tag) / size_block <= max_size_t}) : option (m:bytes{length m = length c - size_tag}) =
  let tg = Seq.slice c 0 size_tag in
  let e = Seq.slice c size_tag (length c) in
  box_open_detached_afternm k n tg e


let box_open_easy (pk:secretkey) (sk:publickey) (n:nonce) (c:bytes{length c >= size_tag /\ (length c - size_tag) / size_block <= max_size_t}) : option (m:bytes{length m = length c - size_tag}) =
  let tg = Seq.slice c 0 size_tag in
  let e = Seq.slice c size_tag (length c) in
  box_open_detached pk sk n tg e
