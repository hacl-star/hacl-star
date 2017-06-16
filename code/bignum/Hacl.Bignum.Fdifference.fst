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

module Hacl.Bignum.Fdifference

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Fdifference

module U32 = FStar.UInt32

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

let gte_limbs_c h (a:felem) h' (b:felem) (l:nat{l <= len}) : GTot Type0 =
  live h a /\ live h' b /\ gte_limbs (as_seq h a) (as_seq h' b) l


[@"substitute"]
val fdifference_:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> gte_limbs_c h a h b len))
    (ensures (fun h0 _ h1 -> gte_limbs_c h0 a h0 b len /\ live h1 a /\ modifies_1 a h0 h1
      /\ as_seq h1 a == fdifference_spec (as_seq h0 a) (as_seq h0 b)))
[@"substitute"]
let rec fdifference_ a b =
  C.Loops.in_place_map2 a b clen (fun x y -> y -%^ x)
