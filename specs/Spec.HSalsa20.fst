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

module Spec.HSalsa20

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open FStar.Endianness
open Seq.Create
open Spec.Lib

module Salsa20 = Spec.Salsa20

let keylen = 32 (* in bytes *)
let blocklen = 64  (* in bytes *)
let noncelen = 16  (* in bytes *)

type key = lbytes keylen
type nonce = lbytes noncelen
type block = lbytes blocklen

type state = Salsa20.state

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

let setup (k:key) (n:nonce): state =
  let ks = uint32s_from_le 8 k in
  let ns = uint32s_from_le 4 n in
  let k_fst_half = slice ks 0 4 in
  let k_snd_half = slice ks 4 8 in
  create_16 Salsa20.constant0 (index ks 0)      (index ks 1)      (index ks 2)
          (index ks 3)       Salsa20.constant1 (index ns 0)      (index ns 1)
	  (index ns 2)       (index ns 3)      Salsa20.constant2 (index ks 4)
          (index ks 5)       (index ks 6)      (index ks 7)      Salsa20.constant3

let hsalsa20 (k:key) (n:nonce) : Tot key = 
  let st = setup k n in
  let st' = Spec.Salsa20.rounds st in
  let hs = create_8 st'.[0] st'.[5] st'.[10] st'.[15] st'.[6] st'.[7] st'.[8] st'.[9] in
  uint32s_to_le 8 hs
