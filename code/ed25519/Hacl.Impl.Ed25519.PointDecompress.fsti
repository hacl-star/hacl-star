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

module Hacl.Impl.Ed25519.PointDecompress

open FStar.Buffer
open Hacl.UInt64
open Hacl.Bignum25519
open Hacl.Impl.Ed25519.ExtPoint


#reset-options "--max_fuel 0 --z3rlimit 20"

val point_decompress:
  out:point ->
  s:buffer UInt8.t{length s = 32} ->
  Stack bool
    (requires (fun h -> live h out /\ live h s))
    (ensures (fun h0 b h1 -> live h0 s /\ live h1 out /\ modifies_1 out h0 h1 /\
      (let px = as_seq h1 (getx out) in let py = as_seq h1 (gety out) in
       let pz = as_seq h1 (getz out) in let pt = as_seq h1 (gett out) in
       (if b then (
         Some? (Spec.Ed25519.point_decompress (as_seq h0 s)) /\
         (seval px, seval py, seval pz, seval pt) == Some?.v (Spec.Ed25519.point_decompress (as_seq h0 s)) /\
         red_513 px /\ red_513 py /\ red_513 pz /\ red_513 pt)
       else None? (Spec.Ed25519.point_decompress (as_seq h0 s)) ))
    ))
