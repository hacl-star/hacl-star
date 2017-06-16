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

module Hacl.Impl.Sha512


open FStar.UInt32
open FStar.Buffer

open Hacl.Impl.SHA512.Ed25519
open Hacl.Spec.Endianness

#reset-options "--max_fuel 0 --z3rlimit 20"

let hint8_p = buffer Hacl.UInt8.t
let op_String_Access h b = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)


val sha512_pre_msg:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{UInt32.v len = length input /\ length input < pow2 32 - 32} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 input /\
      live h1 hash /\ live h1 prefix /\ live h1 input /\ modifies_1 hash h0 h1 /\
      h1.[hash] == Spec.Ed25519.sha512 FStar.Seq.(h0.[prefix] @| h0.[input])))


let sha512_pre_msg h prefix input len =
  sha512_pre_msg h prefix input len


val sha512_pre_pre2_msg:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  prefix2:hint8_p{length prefix2 = 32 /\ disjoint prefix2 hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{UInt32.v len = length input /\ length input < pow2 32 - 64} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h prefix2 /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 input /\ live h0 prefix2 /\
      live h1 hash /\ live h1 prefix /\ live h1 input /\ modifies_1 hash h0 h1 /\
      h1.[hash] == Spec.Ed25519.sha512 FStar.Seq.(h0.[prefix] @| h0.[prefix2] @| h0.[input])))


let sha512_pre_pre2_msg h prefix prefix2 input len =
  sha512_pre_pre2_msg h prefix prefix2 input len
