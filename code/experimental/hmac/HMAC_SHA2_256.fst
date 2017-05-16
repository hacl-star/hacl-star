module HMAC_SHA2_256

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.ST
open FStar.Buffer

open C.Loops

open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module H8 = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64

module Spec_Hash = Spec.SHA2_256
module Hash = Hacl.Hash.SHA2_256
module Spec = Spec.HMAC.SHA2_256
module MAC = Hacl.HMAC.SHA2_256


(* Definition of base types *)
private let uint8_t   = FStar.UInt8.t
private let uint32_t  = FStar.UInt32.t
private let uint64_t  = FStar.UInt64.t

private let uint8_ht  = Hacl.UInt8.t
private let uint32_ht = Hacl.UInt32.t
private let uint64_ht = Hacl.UInt64.t

private let uint32_p = Buffer.buffer uint32_ht
private let uint8_p  = Buffer.buffer uint8_ht


//
// HMAC-SHA2_256
//

val hmac_core:
  mac  :uint8_p  {length mac = v Hash.size_hash} ->
  key  :uint8_p  {length key = v Hash.size_block /\ disjoint key mac} ->
  data :uint8_p  {length data + v Hash.size_block < Spec_Hash.max_input_len_8 /\ disjoint data mac /\ disjoint data key} ->
  len  :uint32_t {length data = v len} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ modifies_1 mac h0 h1))

let hmac_core mac key data len = MAC.hmac_core mac key data len

//
//

val hmac:
  mac     :uint8_p  {length mac = v Hash.size_hash} ->
  key     :uint8_p  {length key = v Hash.size_block /\ disjoint key mac} ->
  keylen  :uint32_t {v keylen = length key} ->
  data    :uint8_p  {length data + v Hash.size_block < Spec_Hash.max_input_len_8 /\ disjoint data mac /\ disjoint data key} ->
  datalen :uint32_t {v datalen = length data} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ modifies_1 mac h0 h1))

let hmac mac key keylen data datalen = MAC.hmac mac key keylen data datalen
