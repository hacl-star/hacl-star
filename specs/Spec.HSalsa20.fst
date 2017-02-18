module Spec.HSalsa20

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open FStar.Endianness
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
  let st = create 16 0ul in
  let st = upd st 0  Spec.Salsa20.constant0 in
  let st = upd st 5  Spec.Salsa20.constant1 in 
  let st = upd st 10 Spec.Salsa20.constant2 in 
  let st = upd st 15 Spec.Salsa20.constant3 in 
  let st = upd st 1  (index ks 0) in
  let st = upd st 2  (index ks 1) in 
  let st = upd st 3  (index ks 2) in 
  let st = upd st 4  (index ks 3) in 
  let st = upd st 11  (index ks 4) in
  let st = upd st 12  (index ks 5) in 
  let st = upd st 13  (index ks 6) in 
  let st = upd st 14  (index ks 7) in 
  let st = upd st 6  (index ns 0) in 
  let st = upd st 7  (index ns 1) in 
  let st = upd st 8  (index ns 2) in 
  let st = upd st 9  (index ns 3) in 
  st

let hsalsa20 (k:key) (n:nonce) : key = 
  let st = setup k n in
  let st' = Spec.Salsa20.rounds st in
  let hs = createL [index st' 0; index st' 5; index st' 10; index st' 15; 
      	   	    index st' 6; index st' 7; index st' 8; index st' 9] in
  uint32s_to_le 8 hs
