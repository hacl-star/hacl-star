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

module Hacl.Bignum.Fscalar

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Fscalar

module U32 = FStar.UInt32

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"


[@"substitute"]
val fscalar:
  output:felem_wide ->
  input:felem{disjoint output input} ->
  s:limb ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 input /\ live h1 output /\ modifies_1 output h0 h1
      /\ as_seq h1 output == fscalar_spec (as_seq h0 input) s))
[@"substitute"]
let fscalar output b s =
  C.Loops.map output b clen (fun x -> Hacl.Bignum.Wide.mul_wide x s)
