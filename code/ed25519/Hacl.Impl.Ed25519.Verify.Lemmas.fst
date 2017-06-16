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

module Hacl.Impl.Ed25519.Verify.Lemmas


open FStar.Mul

let u51 = n:nat{n < 0x8000000000000}

val lemma_equality:
  a:u51 -> b:u51 -> c:u51 -> d:u51 -> e:u51 ->
  a':u51 -> b':u51 -> c':u51 -> d':u51 -> e':u51 ->
  Lemma (requires (a + pow2 51 * b + pow2 102 * c + pow2 153 * d + pow2 204 * e < pow2 255 - 19 /\
                   a' + pow2 51 * b' + pow2 102 * c' + pow2 153 * d' + pow2 204 * e' < pow2 255 - 19))
        (ensures (((a + pow2 51 * b + pow2 102 * c + pow2 153 * d + pow2 204 * e) % (pow2 255 - 19) = (a' + pow2 51 * b' + pow2 102 * c' + pow2 153 * d' + pow2 204 * e') % (pow2 255 - 19)) <==>
          (a == a' /\ b == b' /\ c == c' /\ d == d' /\ e == e')))

#reset-options "--max_fuel 0 --z3rlimit 500"

let lemma_equality a b c d e a' b' c' d' e' =
  assert_norm(pow2 51 = 0x8000000000000);
  assert_norm(pow2 102 = 0x40000000000000000000000000);
  assert_norm(pow2 153 = 0x200000000000000000000000000000000000000);
  assert_norm(pow2 204 = 0x1000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 255 - 19 = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed);
  Math.Lemmas.modulo_lemma (a + pow2 51 * b + pow2 102 * c + pow2 153 * d + pow2 204 * e) (pow2 255 - 19);
  Math.Lemmas.modulo_lemma (a' + pow2 51 * b' + pow2 102 * c' + pow2 153 * d' + pow2 204 * e') (pow2 255 - 19)

