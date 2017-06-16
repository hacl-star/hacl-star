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

module Spec.Curve25519.Lemmas


open FStar.Mul
open FStar.Seq
open FStar.UInt8
open FStar.Endianness

val lemma_prime_value: n:nat -> Lemma
  (requires (n = 255))
  (ensures (pow2 n - 19 = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed))
  [SMTPat (pow2 n - 19)]
let lemma_prime_value n = assert_norm(pow2 255 - 19 = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed)

val lemma_div_n: n:nat -> Lemma
  (requires (n > 1))
  (ensures (n / 2 < n /\ n / 2 > 0))
  [SMTPat (n / 2)]
let lemma_div_n n = ()

val lemma_pow2_256: n:nat -> Lemma
  (requires (n = 256))
  (ensures (pow2 n = 0x10000000000000000000000000000000000000000000000000000000000000000))
  [SMTPat (pow2 n)]
let lemma_pow2_256 n = assert_norm(pow2 256 = 0x10000000000000000000000000000000000000000000000000000000000000000)
