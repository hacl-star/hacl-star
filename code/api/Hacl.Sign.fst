//
//   Copyright 2016-2017  INRIA
//
//   Maintainers: Jean-Karim Zinzindohoué
//                Karthikeyan Bhargavan
//                Benjamin Beurdouche
//
//   Licensed under the Apache License, Version 2.0 (the "License");
//   you may not use this file except in compliance with the License.
//   You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in writing, software
//   distributed under the License is distributed on an "AS IS" BASIS,
//   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//   See the License for the specific language governing permissions and
//   limitations under the License.
//

module Hacl.Sign

open FStar.Buffer
open FStar.ST
open Hacl.Constants


(* Module abbreviations *)
module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"


val crypto_sign_detached:
  sig:uint8_p{length sig = crypto_sign_PUBLICKEYBYTES} ->
  m:uint8_p{length m < pow2 32 - 64 /\ disjoint m sig} ->
  mlen:u32{U32.v mlen = length m} ->
  sk:uint8_p{length sk = crypto_sign_SECRETKEYBYTES /\ disjoint sk sig /\ disjoint sk m} ->
  Stack u32
    (requires (fun h -> live h sig /\ live h m /\ live h sk))
    (ensures (fun h0 _ h1 -> live h0 sig /\ live h0 m /\ live h0 sk
                        /\ live h1 sig /\ modifies_1 sig h0 h1))
let crypto_sign_detached sig m mlen sk =
  Ed25519.sign sig sk m mlen;
  0ul


val crypto_sign:
  sm:uint8_p ->
  smlen:u32{U32.v smlen = length sm} ->
  m:uint8_p{length m < pow2 32 - 64 /\ disjoint sm m} ->
  mlen:u32{U32.v mlen = length m /\ U32.v mlen + crypto_sign_PUBLICKEYBYTES = length sm} ->
  sk:uint8_p{length sk = crypto_sign_SECRETKEYBYTES /\ disjoint sk sm /\ disjoint sk m} ->
  Stack u32
    (requires (fun h -> live h sm /\ live h m /\ live h sk))
    (ensures (fun h0 _ h1 -> live h0 sm /\ live h0 m /\ live h0 sk
                        /\ live h1 sm /\ modifies_1 sm h0 h1))
let crypto_sign sm smlen m mlen sk =
  pop_frame();
  let sig = Buffer.create 0uy 64ul in
  let r = crypto_sign_detached sig m mlen sk in
  let z =
    if U8.(r = 0ul) then (
      Buffer.blit m 0ul sm 0ul mlen;
      Buffer.blit sig 0ul sm mlen 64ul;
      0x0ul)
    else 0xfffffffful in
  pop_frame ();
  z


val crypto_sign_open_detached:
  m:uint8_p{length m < pow2 32 - 64} ->
  mlen:u32{U32.v mlen = length m} ->
  sig:uint8_p{length sig = crypto_sign_PUBLICKEYBYTES /\ disjoint sig m} ->
  pk:uint8_p{length pk = crypto_sign_PUBLICKEYBYTES /\ disjoint pk sig /\ disjoint pk m} ->
  Stack u32
    (requires (fun h -> live h sig /\ live h m /\ live h pk))
    (ensures (fun h0 _ h1 -> live h0 sig /\ live h0 m /\ live h0 pk
                        /\ live h1 sig /\ modifies_0 h0 h1))
let crypto_sign_open_detached m mlen sig pk =
  let verify = Ed25519.verify pk m mlen sig in
  let z =
    if U8.(verify = true) then 0x0ul else 0xfffffffful in
  z


val crypto_sign_open:
  m:uint8_p{length m < pow2 32 - 64} ->
  mlen:u32{U32.v mlen = length m} ->
  sm:uint8_p{length sm = length m + crypto_sign_PUBLICKEYBYTES /\ disjoint sm m}->
  smlen:u32{U32.v smlen = length sm} ->
  pk:uint8_p{length pk = crypto_sign_PUBLICKEYBYTES /\ disjoint pk m /\ disjoint pk sm} ->
  Stack u32
    (requires (fun h -> live h sm /\ live h m /\ live h pk))
    (ensures (fun h0 _ h1 -> live h0 sm /\ live h0 m /\ live h0 pk
                        /\ live h1 sm /\ modifies_1 sm h0 h1))
let crypto_sign_open m mlen sm smlen pk =
  let sig = Buffer.sub sm (U32.sub smlen 64ul) 64ul in
  let verify = crypto_sign_open_detached m mlen sig pk in
  let z =
    if U8.(verify = 0ul) then (
      Buffer.blit sm 0ul m 0ul (U32.sub smlen 64ul);
      0x0ul )
    else 0xfffffffful in
  z
