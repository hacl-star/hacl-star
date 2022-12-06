module Hacl.Hash.Blake2

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module BlB32 = Hacl.Blake2b_32
open Lib.IntTypes

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"

friend Spec.Agile.Hash

let alloca_blake2b_32 () =
  let h0 = ST.get() in
  let s = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2B M32 in
  BlB32.blake2b_init s 0ul 64ul;
  let h1 = ST.get () in
  B.modifies_only_not_unused_in (B.loc_none) h0 h1;
  assert (B.modifies B.loc_none h0 h1);
  s, u128 0

let init_blake2b_32 s = BlB32.blake2b_init s 0ul 64ul

// AF: TODO, The implementation in Hacl.Impl.Blake2.Generic currently expects the length of blocks as an implicit... This does not seem needed, we should remove it
// let update_multi_blake2b_32 s ev blocks n = BlB32.blake2b_update_multi s ev blocks n
