module Fswap_inline

open X64.CPU_Features_s
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
open Fast_defs
open FStar.Mul

unfold
let u256 = b:B.buffer UInt64.t{B.length b == 4}
unfold
let u512 = b:B.buffer UInt64.t{B.length b == 8}
unfold
let u1024 = b:B.buffer UInt64.t{B.length b == 16}

let as_nat (b:B.buffer UInt64.t{B.length b == 4}) (h:HS.mem) : GTot nat =
  let s = B.as_seq h b in
  let s0 = UInt64.v (Seq.index s 0) in
  let s1 = UInt64.v (Seq.index s 1) in
  let s2 = UInt64.v (Seq.index s 2) in
  let s3 = UInt64.v (Seq.index s 3) in
  pow2_four s0 s1 s2 s3

val cswap2_inline
  (p0:u512)
  (p1:u512)
  (bit:UInt64.t{UInt64.v bit <= 1})
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
