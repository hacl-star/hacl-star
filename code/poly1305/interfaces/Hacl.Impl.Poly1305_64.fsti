module Hacl.Impl.Poly1305_64


open FStar.Mul
open FStar.ST
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.Endianness
open FStar.Buffer

open Hacl.Spec.Endianness
open Hacl.Endianness

inline_for_extraction let log_t = erased (Spec.Poly1305.text)

inline_for_extraction let bigint = b:buffer Hacl.UInt64.t{length b = 3}
inline_for_extraction let uint8_p = buffer Hacl.UInt8.t

let elemB : Type0  = b:bigint

let wordB : Type0  = b:uint8_p{length b <= 16}
let wordB_16 : Type0 = b:uint8_p{length b = 16}


noeq type poly1305_state = | MkState: r:bigint -> h:bigint -> poly1305_state

let live_st m (st:poly1305_state) : Type0 =
  live m st.h /\ live m st.r /\ disjoint st.h st.r
