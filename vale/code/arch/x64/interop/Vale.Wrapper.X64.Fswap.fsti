module Vale.Wrapper.X64.Fswap

open Vale.X64.CPU_Features_s
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
open Vale.Curve25519.Fast_defs
open FStar.Mul
open Vale.Wrapper.X64.Fadd

inline_for_extraction
val cswap2_e
  (bit:UInt64.t{UInt64.v bit <= 1})
  (p0:u512)
  (p1:u512)
  : Stack unit
    (requires fun h ->
      B.live h p0 /\ B.live h p1 /\
      (B.disjoint p0 p1 \/ p0 == p1))
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_union (B.loc_buffer p0) (B.loc_buffer p1)) h0 h1 /\
      (let old_p0 = B.as_seq h0 p0 in
      let new_p0 = B.as_seq h1 p0 in
      let old_p1 = B.as_seq h0 p1 in
      let new_p1 = B.as_seq h1 p1 in
      (UInt64.v bit = 1 ==> (Seq.equal old_p0 new_p1 /\ Seq.equal old_p1 new_p0)) /\
      (UInt64.v bit = 0 ==> (Seq.equal old_p0 new_p0 /\ Seq.equal old_p1 new_p1))
      )
    )
