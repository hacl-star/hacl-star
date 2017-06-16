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

module Hacl.Impl.Ed25519.RecoverX

open FStar.Mul
open FStar.Buffer
open FStar.UInt64
open Hacl.Bignum25519
open Hacl.Impl.Ed25519.Pow2_252m2

let elemB = b:buffer Hacl.UInt64.t{length b = 5}


#reset-options "--max_fuel 0 --z3rlimit 100"

val recover_x:
  x:elemB ->
  y:elemB{disjoint x y} ->
  sign:UInt64.t{v sign = 0 \/ v sign = 1} ->
  Stack bool
    (requires (fun h -> live h x /\ live h y /\ red_51 (as_seq h y)))
    (ensures (fun h0 z h1 -> live h1 x /\ live h0 y /\ modifies_1 x h0 h1 /\
      (let op_String_Access = Seq.index in
       let y = as_seq h0 y in
       let y:nat = v y.[0] + pow2 51 * v y.[1] + pow2 102 * v y.[2] + pow2 153 * v y.[3]
               + pow2 204 * v y.[4] in
       let x = as_seq h1 x in
       let sign = (v sign = 1) in
       let res  = Spec.Ed25519.recover_x y sign in
       (z <==> Some? res)
       /\ (Some? res ==> (seval x = Some?.v res /\ red_51 x)))
      ))
