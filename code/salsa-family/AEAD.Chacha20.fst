module AEAD.Chacha20

open FStar.Mul
open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.UInt32
open Hacl.Spec.Endianness
open Hacl.Endianness

open Hacl.Impl.Chacha20
module Spec = Spec.Chacha20

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32


val chacha_key_block:
  block:uint8_p{length block = 64} ->
  k:uint8_p{length k = 32 /\ disjoint block k} ->
  n:uint8_p{length k = 12 /\ disjoint block n} ->
  ctr:UInt32.t ->
  Stack unit
    (requires (fun h -> live h block /\ live h k))
    (ensures (fun h0 _ h1 -> live h1 block /\ modifies_1 block h0 h1))
let chacha_key_block block k n ctr =
  let st = alloc () in
  let _  = setup st k n ctr in
  let _  = chacha20_block (Ghost.hide (MkLog Seq.createEmpty Seq.createEmpty)) block st ctr in
  ()
