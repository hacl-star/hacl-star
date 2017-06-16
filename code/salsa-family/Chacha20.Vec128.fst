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

module Chacha20.Vec128


open FStar.Buffer


#reset-options "--max_fuel 0 --z3rlimit 20"


open Hacl.Impl.Chacha20.Vec128
open Hacl.Spec.Endianness

let chacha20 output plain len k n ctr =
  let h0 = ST.get() in
  chacha20 output plain len k n ctr;
  let h1 = ST.get() in
  Spec.Chacha20_vec1.Lemmas.lemma_chacha20_encrypt_bytes (reveal_sbytes (as_seq h0 k)) (reveal_sbytes (as_seq h0 n)) (UInt32.v ctr) (reveal_sbytes (as_seq h0 plain))
