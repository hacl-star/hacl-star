module Hacl.Hash

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module B = LowStar.Buffer
module S = FStar.Seq
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module Tactics = FStar.Tactics

module MD5 = Hacl.MD5
module SHA1 = Hacl.SHA1

open Hacl.Hash.Common
open Hacl.Hash.Lemmas
open Spec.Hash
open FStar.Mul

#set-options "--max_fuel 1 --max_ifuel 0 --z3rlimit 128"

noextract
let mk_update_multi a update s blocks n_blocks =
  let h0 = ST.get () in
  let inv (h: HS.mem) (i: nat) =
    let i_block = size_block a * i in
    i <= U32.v n_blocks /\
    B.live h s /\ B.live h blocks /\
    B.(modifies (loc_buffer s) h0 h) /\
    S.equal (B.as_seq h s)
      (update_multi a (B.as_seq h0 s) (S.slice (B.as_seq h0 blocks) 0 i_block))
  in
  let f (i:U32.t { U32.(0 <= v i /\ v i < v n_blocks)}): ST.Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun h0 _ h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1)))
  =
    let h1 = ST.get () in
    let sz = size_block_ul a in
    let blocks0 = B.sub blocks 0ul U32.(sz *^ i) in
    let block = B.sub blocks U32.(sz *^ i) sz in
    update s block;
    let h2 = ST.get () in
    assert (
      let s0 = B.as_seq h0 s in
      let s1 = B.as_seq h1 s in
      let s2 = B.as_seq h2 s in
      let blocks = B.as_seq h0 blocks in
      let block = B.as_seq h0 block in
      let blocks0 = B.as_seq h0 blocks0 in
      let i = U32.v i in
      let n_blocks = U32.v n_blocks in
      size_block a * (i + 1) <= S.length blocks /\
      (size_block a * (i + 1) - size_block a * i) % size_block a = 0 /\
      S.equal block (S.slice blocks (size_block a * i) (size_block a * (i + 1))) /\
      S.equal s2 (update_multi a s1 block))
  in
  assert (B.length blocks = U32.v n_blocks * size_block a);
  C.Loops.for 0ul n_blocks inv f

let update_multi_sha2_224: update_multi_t SHA2_224 =
  Tactics.(synth_by_tactic
    (specialize (mk_update_multi SHA2_224 Hacl.SHA2.update_224) [`%mk_update_multi]))

let update_multi_sha2_256: update_multi_t SHA2_256 =
  Tactics.(synth_by_tactic
    (specialize (mk_update_multi SHA2_256 Hacl.SHA2.update_256) [`%mk_update_multi]))

let update_multi_sha2_384: update_multi_t SHA2_384 =
  Tactics.(synth_by_tactic
    (specialize (mk_update_multi SHA2_384 Hacl.SHA2.update_384) [`%mk_update_multi]))

let update_multi_sha2_512: update_multi_t SHA2_512 =
  Tactics.(synth_by_tactic
    (specialize (mk_update_multi SHA2_512 Hacl.SHA2.update_512) [`%mk_update_multi]))

let update_multi_sha1: update_multi_t SHA1 =
  Tactics.(synth_by_tactic
    (specialize (mk_update_multi SHA1 Hacl.SHA1.update) [`%mk_update_multi]))

let update_multi_md5: update_multi_t MD5 =
  Tactics.(synth_by_tactic
    (specialize (mk_update_multi MD5 Hacl.MD5.update) [`%mk_update_multi]))
