module Spec.HSalsa20

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open FStar.Endianness
open Seq.Create
open Spec.Lib

let keylen = 32 (* in bytes *)
let blocklen = 64  (* in bytes *)
let noncelen = 16  (* in bytes *)

type key = lbytes keylen
type nonce = lbytes noncelen
type block = lbytes blocklen

type state = Spec.Salsa20.state

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

let setup (k:key) (n:nonce): state =
  let ks = uint32s_from_le 8 k in
  let ns = uint32s_from_le 4 n in
  let k_fst_half = slice ks 0 4 in
  let k_snd_half = slice ks 4 8 in
  let c0 = singleton (Spec.Salsa20.constant0) in
  let c1 = singleton (Spec.Salsa20.constant1) in
  let c2 = singleton (Spec.Salsa20.constant2) in
  let c3 = singleton (Spec.Salsa20.constant3) in
  c0 @| k_fst_half @| c1 @| ns @| c2 @| k_snd_half @| c3

let hsalsa20 (k:key) (n:nonce) : Tot key = 
  let st = setup k n in
  let st' = Spec.Salsa20.rounds st in
  let hs = create_8 st'.[0] st'.[5] st'.[10] st'.[15] st'.[6] st'.[7] st'.[8] st'.[9] in
  uint32s_to_le 8 hs
