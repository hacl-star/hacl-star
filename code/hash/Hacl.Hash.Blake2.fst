module Hacl.Hash.Blake2

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module BlB32 = Hacl.Blake2b_32
open Lib.IntTypes
open Lib.Buffer

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"

friend Spec.Agile.Hash

let alloca_blake2b_32 () =
  let h0 = ST.get() in
  let s = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2B M32 in
  BlB32.blake2b_init s 0ul 64ul;
  let h1 = ST.get () in
  B.modifies_only_not_unused_in (B.loc_none) h0 h1;
  assert (B.modifies B.loc_none h0 h1);
  s

let init_blake2b_32 s = BlB32.blake2b_init s 0ul 64ul

let update_multi_blake2b_32 s ev blocks n =
  ST.push_frame ();
  let wv = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2B M32 in
  BlB32.blake2b_update_multi #(n `FStar.UInt32.mul` block_len Blake2B) wv s ev blocks n;
  ST.pop_frame ()

let update_last_blake2b_32 s prev input input_len =
  ST.push_frame ();
  let wv = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2B M32 in
  BlB32.blake2b_update_last #input_len wv s (secret prev) input_len input;
  ST.pop_frame()

let finish_blake2b_32 s dst = BlB32.blake2b_finish (hash_len Blake2B) dst s
