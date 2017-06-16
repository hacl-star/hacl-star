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

module Hacl.Impl.Ed25519.Pow2_252m2

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum25519

val pow2_252m2:
  out:felem ->
  z:felem{disjoint out z} ->
  Stack unit
  (requires (fun h -> live h out /\ live h z /\ red_513 (as_seq h z)))
  (ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1 /\ live h0 z
    /\ red_513 (as_seq h0 z)
    /\ seval (as_seq h1 out) == Spec.Curve25519.(seval (as_seq h0 z) ** ((prime + 3) / 8))
    /\ red_513 (as_seq h1 out)
  ))
