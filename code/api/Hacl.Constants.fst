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

module Hacl.Constants

(* Type abbreviations *)
type u8  = FStar.UInt8.t
type u32 = FStar.UInt32.t
type u64 = FStar.UInt64.t

type h8  = Hacl.UInt8.t
type h32  = Hacl.UInt32.t
type h64  = Hacl.UInt64.t

type uint8_p = FStar.Buffer.buffer h8

(* Size constants (for specifications) *)
let crypto_box_NONCEBYTES     = 24
let crypto_box_PUBLICKEYBYTES = 32
let crypto_box_SECRETKEYBYTES = 32
let crypto_box_MACBYTES       = 16

let crypto_secretbox_NONCEBYTES = 24
let crypto_secretbox_KEYBYTES   = 32
let crypto_secretbox_MACBYTES   = 16
