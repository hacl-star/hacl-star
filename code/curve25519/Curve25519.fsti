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

module Curve25519

open FStar.Buffer

#reset-options "--max_fuel 0 --z3rlimit 20"

type uint8_p = Buffer.buffer Hacl.UInt8.t

let op_String_Access h (b:uint8_p{live h b}) = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)

val crypto_scalarmult:
  mypublic:uint8_p{length mypublic = 32} ->
  secret:uint8_p{length secret = 32} ->
  point:uint8_p{length point = 32} ->
  Stack unit
    (requires (fun h -> live h mypublic /\ live h secret /\ live h point))
    (ensures (fun h0 _ h1 -> live h1 mypublic /\ modifies_1 mypublic h0 h1 /\
     live h0 mypublic /\ live h0 secret /\ live h0 point /\
     h1.[mypublic] == Spec.Curve25519.(scalarmult h0.[secret] h0.[point])))
