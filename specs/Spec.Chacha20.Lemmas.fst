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

module Spec.Chacha20.Lemmas

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open FStar.Endianness
open Spec.Lib

val lemma_seq_cons_4: #a:Type -> x:a -> y:a -> z:a -> w:a -> Lemma
  (requires (True))
  (ensures (length (createL [x; y; z; w]) = 4))
  [SMTPat (createL [x; y; z; w])]
let lemma_seq_cons_4 #a x y z w = assert_norm(List.Tot.length [x; y; z; w] = 4)
