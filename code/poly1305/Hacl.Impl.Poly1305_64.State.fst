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

module Hacl.Impl.Poly1305_64.State

open FStar.Buffer
open FStar.Ghost

open Hacl.UInt64

include Hacl.Spec.Poly1305_64.State

inline_for_extraction let log_t = erased (Spec.Poly1305.text)
inline_for_extraction let uint8_p = buffer Hacl.UInt8.t

inline_for_extraction let bigint  = b:Buffer.buffer Hacl.UInt64.t{Buffer.length b = 3}
let seqelem = s:Seq.seq Hacl.UInt64.t{Seq.length s = 3}

let elemB : Type0  = b:bigint

let wordB : Type0  = b:uint8_p{length b <= 16}
let wordB_16 : Type0 = b:uint8_p{length b = 16}

noeq type poly1305_state =  | MkState: r:bigint -> h:bigint -> poly1305_state
  (* {r:bigint; h:bigint} *)

let live_st m (st:poly1305_state) : Type0 =
  live m st.h /\ live m st.r /\ disjoint st.h st.r
