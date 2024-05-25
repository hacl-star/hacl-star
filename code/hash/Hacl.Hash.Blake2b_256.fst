module Hacl.Hash.Blake2b_256

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module BlB256 = Hacl.Blake2b_256
open Lib.IntTypes
open Lib.Buffer

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"

friend Spec.Agile.Hash

let malloc = BlB256.malloc_with_key

let alloca () =
  let h0 = ST.get() in
  let s = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2B M256 in
  BlB256.init s 0ul 64ul;
  let h1 = ST.get () in
  B.modifies_only_not_unused_in (B.loc_none) h0 h1;
  assert (B.modifies B.loc_none h0 h1);
  s

let init s = BlB256.init s 0ul 64ul

let update_multi s ev blocks n =
  ST.push_frame ();
  let wv = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2B M256 in
  BlB256.update_multi #(n `FStar.UInt32.mul` block_len Blake2B) wv s (secret ev) blocks n;
  ST.pop_frame ()

let update_last s prev input input_len =
  ST.push_frame ();
  let wv = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2B M256 in
  BlB256.update_last #input_len wv s false (secret prev) input_len input;
  ST.pop_frame()

let finish s dst = BlB256.finish (hash_len Blake2B) dst s

let hash output input input_len = Hacl.Streaming.Blake2b_256.hash_with_key output 64ul input input_len (null #MUT uint8) 0ul
