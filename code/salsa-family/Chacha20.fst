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

module Chacha20

open FStar.Buffer
open Hacl.Spec.Endianness
open Hacl.Impl.Chacha20

module U32 = FStar.UInt32

#reset-options "--max_fuel 0 --z3rlimit 100"

let chacha20_key_block block k n ctr =
  push_frame();
  let st = alloc () in
  let l  = init st k n in
  let l  = chacha20_block l block st ctr in
  pop_frame()

let chacha20 output plain len k n ctr = chacha20 output plain len k n ctr
