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

module Hacl.Impl.Ed25519.SecretToPublic

open FStar.HyperStack
open FStar.Buffer

#reset-options "--max_fuel 0 --z3rlimit 20"

let hint8_p = buffer Hacl.UInt8.t
let op_String_Access h b = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)

val secret_to_public:
  out:hint8_p{length out = 32} ->
  secret:hint8_p{length secret = 32 /\ disjoint out secret} ->
  Stack unit
    (requires (fun h -> live h out /\ live h secret))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 secret /\ live h1 out /\ modifies_1 out h0 h1 /\
      h1.[out] == Spec.Ed25519.secret_to_public h0.[secret]))
