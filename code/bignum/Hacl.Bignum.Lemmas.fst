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

module Hacl.Bignum.Lemmas


(* Bound lemmas associated to SMT patterns *)

(* let lemma_max_uint8 (n:nat) : Lemma *)
(*   (requires (n = 8)) *)
(*   (ensures (pow2 n = 256)) *)
(*   [SMTPat (pow2 n)] *)
(*   = assert_norm(pow2 8 = 256) *)
(* let lemma_max_uint32 (n:nat) : Lemma *)
(*   (requires (n = 32)) *)
(*   (ensures (pow2 n = 4294967296)) *)
(*   [SMTPat (pow2 n)] *)
(*   = assert_norm(pow2 32 = 4294967296) *)
(* let lemma_max_uint64 (n:nat) : Lemma *)
(*   (requires (n = 64)) *)
(*   (ensures (pow2 n = 18446744073709551616)) *)
(*   [SMTPat (pow2 n)] *)
(*   = assert_norm(pow2 64 = 18446744073709551616) *)
(* let lemma_max_uint128 (n:nat) : Lemma *)
(*   (requires (n = 128)) *)
(*   (ensures (pow2 n = 340282366920938463463374607431768211456)) *)
(*   [SMTPat (pow2 n)] *)
(*   = assert_norm(pow2 128 = 340282366920938463463374607431768211456) *)
(* let lemma_2_51 (n:nat) : Lemma *)
(*   (requires (n = 51)) *)
(*   (ensures (pow2 n = 2251799813685248)) *)
(*   [SMTPat (pow2 n)] *)
(*   = assert_norm(pow2 51 = 2251799813685248) *)
(* let lemma_2_102 (n:nat) : Lemma *)
(*   (requires (n = 102)) *)
(*   (ensures (pow2 n = 5070602400912917605986812821504)) *)
(*   [SMTPat (pow2 n)] *)
(*   = assert_norm(pow2 102 = 5070602400912917605986812821504) *)
(* let lemma_2_153 (n:nat) : Lemma  *)
(*   (requires (n = 153)) *)
(*   (ensures (pow2 n = 11417981541647679048466287755595961091061972992)) *)
(*   [SMTPat (pow2 n)] *)
(*   = assert_norm(pow2 153 = 11417981541647679048466287755595961091061972992) *)
(* let lemma_2_204 (n:nat) : Lemma  *)
(*   (requires (n = 204)) *)
(*   (ensures (pow2 n = 25711008708143844408671393477458601640355247900524685364822016)) *)
(*   [SMTPat (pow2 n)] *)
(*   = assert_norm(pow2 204 = 25711008708143844408671393477458601640355247900524685364822016) *)
(* let lemma_2_255 (n:nat) : Lemma  *)
(*   (requires (n = 255)) *)
(*   (ensures (pow2 n = 57896044618658097711785492504343953926634992332820282019728792003956564819968)) *)
(*   [SMTPat (pow2 n)] *)
(*   = assert_norm(pow2 255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968) *)
