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

module Hacl.Impl.Store51

open FStar.Buffer
open FStar.Endianness
open FStar.Mul

open Hacl.UInt64
open Hacl.Spec.Endianness
open Hacl.Endianness


#reset-options "--max_fuel 0 --z3rlimit 100"

[@ "substitute"]
val store_51:
  output:buffer Hacl.UInt8.t{Buffer.length output = 32} ->
  input:buffer Hacl.UInt64.t{Buffer.length input = 5} ->
  Stack unit
    (requires (fun h -> Buffer.live h input /\
      Hacl.Bignum25519.red_51 (as_seq h input) /\
      (let s = as_seq h input in v (Seq.index s 0) + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2) + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4) < pow2 255 - 19) /\
      Buffer.live h output))
    (ensures (fun h0 _ h1 -> Buffer.live h0 input /\ Buffer.live h1 input /\
      modifies_1 output h0 h1 /\
      Buffer.live h1 output /\
      hlittle_endian (as_seq h1 output) == Hacl.Bignum25519.seval (as_seq h0 input)))
