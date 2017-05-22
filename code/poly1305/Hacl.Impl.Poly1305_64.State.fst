module Hacl.Impl.Poly1305_64.State

open FStar.Buffer
open Hacl.UInt64

let bigint  = b:Buffer.buffer Hacl.UInt64.t{Buffer.length b = 3}
let seqelem = s:Seq.seq Hacl.UInt64.t{Seq.length s = 3}

noeq type poly1305_state =  {r:bigint; h:bigint}

let live_st m (st:poly1305_state) : Type0 =
  live m st.h /\ live m st.r /\ disjoint st.h st.r

inline_for_extraction let p44 : p:pos{p = 0x100000000000} = assert_norm (pow2 44 = 0x100000000000);
  pow2 44
inline_for_extraction let p45 : p:pos{p = 0x200000000000} = assert_norm (pow2 45 = 0x200000000000);
  pow2 45

let red_44 (s:seqelem) =
  v (Seq.index s 0) < p44 /\ v (Seq.index s 1) < p44 /\ v (Seq.index s 2) < p44
let red_45 (s:seqelem) =
  v (Seq.index s 0) < p45 /\ v (Seq.index s 1) < p45 /\ v (Seq.index s 2) < p45
