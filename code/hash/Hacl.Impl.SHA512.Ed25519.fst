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

module Hacl.Impl.SHA512.Ed25519

open FStar.Mul
open FStar.UInt32
open FStar.HyperStack
open FStar.Seq
open FStar.Buffer

#reset-options "--max_fuel 0 --z3rlimit 20"

open Hacl.Impl.SHA512.Ed25519_3

let sha512_pre_msg h prefix input len =
  sha512_pre_msg h prefix input len

let sha512_pre_pre2_msg h prefix prefix2 input len =
  sha512_pre_pre2_msg h prefix prefix2 input len
