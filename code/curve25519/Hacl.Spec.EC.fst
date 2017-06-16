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

module Hacl.Spec.EC

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Spec.Endianness
open Hacl.Spec.EC.Point
open Hacl.Spec.EC.Format
open Hacl.Spec.EC.Ladder


module U32 = FStar.UInt32
module H8 = Hacl.UInt8


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val crypto_scalarmult_spec:
  secret:uint8_s{Seq.length secret = 32} ->
  basepoint:uint8_s{Seq.length basepoint = 32} ->
  GTot (mypublic:uint8_s{Seq.length mypublic = 32 /\ (
    let mypublic  = reveal_sbytes mypublic in
    let secret    = reveal_sbytes secret in
    let basepoint = reveal_sbytes basepoint in
    mypublic == Spec.Curve25519.scalarmult secret basepoint)
    })
let crypto_scalarmult_spec secret basepoint =
  let q = point_of_scalar basepoint in
  let scalar = format_secret secret in
  let res = cmult_spec scalar q in
  scalar_of_point res
