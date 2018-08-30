module Hacl.Hash

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module B = LowStar.Buffer
module S = FStar.Seq
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open Hacl.Hash.Lemmas
open Spec.Hash
open FStar.Mul

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

let mk_update_multi a update s blocks n_blocks =
  let h0 = ST.get () in
  let inv (h: HS.mem) (i: nat) =
    let i_block = size_block a * i in
    i <= U64.v n_blocks /\
    B.live h s /\ B.live h blocks /\
    B.(modifies (loc_buffer s) h0 h) /\
    S.equal (B.as_seq h s)
      (update_multi a (B.as_seq h0 s) (S.slice (B.as_seq h0 blocks) 0 i_block))
  in
  let f (i:U64.t { U64.(0 <= v i /\ v i < v n_blocks)}): ST.Stack unit
    (requires (fun h -> inv h (U64.v i)))
    (ensures (fun h0 _ h1 -> inv h0 (U64.v i) /\ inv h1 (U64.v i + 1)))
  =
    admit ()
  in
  assert (B.length blocks = U64.v n_blocks * size_block a);
  C.Loops.for64 0UL n_blocks inv f
