module Hacl.Impl.Poly1305_32.State

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Buffer
open FStar.Ghost

open Hacl.UInt64

include Hacl.Spec.Poly1305_32.State

inline_for_extraction let log_t = erased (Spec.Poly1305.text)
inline_for_extraction let uint8_p = buffer Hacl.UInt8.t

inline_for_extraction let bigint  = b:Buffer.buffer Hacl.UInt32.t{Buffer.length b = 5}
let seqelem = s:Seq.seq Hacl.UInt32.t{Seq.length s = 5}

let elemB : Type0  = b:bigint

let wordB : Type0  = b:uint8_p{length b <= 16}
let wordB_16 : Type0 = b:uint8_p{length b = 16}

noeq type poly1305_state =  | MkState: r:bigint -> h:bigint -> poly1305_state

let live_st m (st:poly1305_state) : Type0 =
  live m st.h /\ live m st.r /\ disjoint st.h st.r
