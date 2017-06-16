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

module Hacl.Bignum.Fsum

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Fsum

module U32 = FStar.UInt32

#reset-options "--max_fuel 0 --z3rlimit 20"

let red_c h (f:felem) ctr = live h f /\ red (as_seq h f) ctr

[@"substitute"]
val fsum_:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> red_c h a len /\ red_c h b len))
    (ensures (fun h0 _ h1 -> red_c h0 a len /\ red_c h0 b len /\ live h1 a /\ modifies_1 a h0 h1
      /\ as_seq h1 a == fsum_spec (as_seq h0 a) (as_seq h0 b)))
[@"substitute"]
let rec fsum_ a b =
  C.Loops.in_place_map2 a b clen (fun x y -> x +%^ y)
