
module Spec.HMAC

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module HA=Spec.Hash.Definitions
module HP=Spec.Hash.PadFinish
module H = Spec.Hash


(* Key wrapping function *)
let wrap_key a key =
  let block = create (HA.block_length a) (u8 0) in
  let len = length key in
  if len <= HA.block_length a then
     update_slice block 0 len key
  else
    let nkey = H.hash a key in
    update_slice block 0 (HA.hash_length a) nkey

#set-options "--z3rlimit 200"

(* HMAC *)
let hmac a key input = 
  let ipad = create (HA.block_length a) (u8 0x36) in
  let opad = create (HA.block_length a) (u8 0x5c) in
  let key' = wrap_key a key in
  let ikey = map2 (fun x y -> logxor x y) ipad key' in
  let okey = map2 (fun x y -> logxor x y) opad key' in
  H.hash a FStar.Seq.(okey @| H.hash a (ikey @| input))

