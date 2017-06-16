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

module Hacl.Impl.Load51

open FStar.Mul
open FStar.Buffer
open FStar.Endianness

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Endianness
open Hacl.UInt64

open Hacl.Spec.Endianness

#reset-options "--max_fuel 0 --z3rlimit 10"

let u32 = UInt32.t
let h8 = Hacl.UInt8.t
let h64 = Hacl.UInt64.t
let hint8_p = buffer h8

val load_51: output:felem -> input:hint8_p{length input = 32} -> Stack unit
  (requires (fun h -> Buffer.live h output /\ Buffer.live h input))
  (ensures (fun h0 _ h1 -> Buffer.live h0 output /\ Buffer.live h0 input
    /\ Buffer.live h1 output /\ modifies_1 output h0 h1
    /\ Hacl.Bignum25519.red_51 (as_seq h1 output)
    /\ (let out = reveal_h64s (as_seq h1 output) in
       let open FStar.UInt64 in
       v (Seq.index out 0) + pow2 51 * v (Seq.index out 1) + pow2 102 * v (Seq.index out 2)  + pow2 153 * v (Seq.index out 3)  + pow2 204 * v (Seq.index out 4) == hlittle_endian (as_seq h0 input) % pow2 255)))
