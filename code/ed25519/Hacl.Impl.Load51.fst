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

module Hacl.Impl.Load51

open FStar.Mul
open FStar.Buffer
open FStar.Endianness

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Endianness
open Hacl.UInt64


#reset-options "--max_fuel 0 --z3rlimit 100"

let load_51 output input =
  Hacl.EC.Format.fexpand output input;
  let h = ST.get() in
  Hacl.Bignum25519.lemma_reveal_seval (as_seq h output);
  Hacl.Bignum25519.lemma_intro_red_51 (as_seq h output);
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 (as_seq h output)
