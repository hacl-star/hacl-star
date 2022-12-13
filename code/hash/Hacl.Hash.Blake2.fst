module Hacl.Hash.Blake2

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module BlB32 = Hacl.Blake2b_32
module BlB256 = Hacl.Blake2b_256
module BlS32 = Hacl.Blake2s_32
module BlS128 = Hacl.Blake2s_128
open Lib.IntTypes
open Lib.Buffer

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"

friend Spec.Agile.Hash

// Blake2b_32

let malloc_blake2b_32 = BlB32.blake2b_malloc

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
  BlB32.blake2b_update_multi #(n `FStar.UInt32.mul` block_len Blake2B) wv s (secret ev) blocks n;
  ST.pop_frame ()

let update_last_blake2b_32 s prev input input_len =
  ST.push_frame ();
  let wv = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2B M32 in
  BlB32.blake2b_update_last #input_len wv s (secret prev) input_len input;
  ST.pop_frame()

let finish_blake2b_32 s dst = BlB32.blake2b_finish (hash_len Blake2B) dst s

let hash_blake2b_32 input input_len dst = BlB32.blake2b 64ul dst input_len input 0ul (null #MUT uint8)

// Blake2s_32

let malloc_blake2s_32 = BlS32.blake2s_malloc

let alloca_blake2s_32 () =
  let h0 = ST.get() in
  let s = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2S M32 in
  BlS32.blake2s_init s 0ul 32ul;
  let h1 = ST.get () in
  B.modifies_only_not_unused_in (B.loc_none) h0 h1;
  assert (B.modifies B.loc_none h0 h1);
  s

let init_blake2s_32 s = BlS32.blake2s_init s 0ul 32ul

let update_multi_blake2s_32 s ev blocks n =
  ST.push_frame ();
  let wv = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2S M32 in
  BlS32.blake2s_update_multi #(n `FStar.UInt32.mul` block_len Blake2S) wv s (secret ev) blocks n;
  ST.pop_frame ()

let update_last_blake2s_32 s prev input input_len =
  ST.push_frame ();
  let wv = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2S M32 in
  BlS32.blake2s_update_last #input_len wv s (secret prev) input_len input;
  ST.pop_frame()

let finish_blake2s_32 s dst = BlS32.blake2s_finish (hash_len Blake2S) dst s

let hash_blake2s_32 input input_len dst = BlS32.blake2s 32ul dst input_len input 0ul (null #MUT uint8)

// Blake2s_128

let malloc_blake2s_128 = BlS128.blake2s_malloc

let alloca_blake2s_128 () =
  let h0 = ST.get() in
  let s = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2S M128 in
  BlS128.blake2s_init s 0ul 32ul;
  let h1 = ST.get () in
  B.modifies_only_not_unused_in (B.loc_none) h0 h1;
  assert (B.modifies B.loc_none h0 h1);
  s

let init_blake2s_128 s = BlS128.blake2s_init s 0ul 32ul

let update_multi_blake2s_128 s ev blocks n =
  ST.push_frame ();
  let wv = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2S M128 in
  BlS128.blake2s_update_multi #(n `FStar.UInt32.mul` block_len Blake2S) wv s (secret ev) blocks n;
  ST.pop_frame ()

let update_last_blake2s_128 s prev input input_len =
  ST.push_frame ();
  let wv = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2S M128 in
  BlS128.blake2s_update_last #input_len wv s (secret prev) input_len input;
  ST.pop_frame()

let finish_blake2s_128 s dst = BlS128.blake2s_finish (hash_len Blake2S) dst s

let hash_blake2s_128 input input_len dst = BlS128.blake2s 32ul dst input_len input 0ul (null #MUT uint8)

// Blake2b_256

let malloc_blake2b_256 = BlB256.blake2b_malloc

let alloca_blake2b_256 () =
  let h0 = ST.get() in
  let s = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2B M256 in
  BlB256.blake2b_init s 0ul 64ul;
  let h1 = ST.get () in
  B.modifies_only_not_unused_in (B.loc_none) h0 h1;
  assert (B.modifies B.loc_none h0 h1);
  s

let init_blake2b_256 s = BlB256.blake2b_init s 0ul 64ul

let update_multi_blake2b_256 s ev blocks n =
  ST.push_frame ();
  let wv = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2B M256 in
  BlB256.blake2b_update_multi #(n `FStar.UInt32.mul` block_len Blake2B) wv s (secret ev) blocks n;
  ST.pop_frame ()

let update_last_blake2b_256 s prev input input_len =
  ST.push_frame ();
  let wv = Hacl.Impl.Blake2.Core.alloc_state Spec.Blake2.Blake2B M256 in
  BlB256.blake2b_update_last #input_len wv s (secret prev) input_len input;
  ST.pop_frame()

let finish_blake2b_256 s dst = BlB256.blake2b_finish (hash_len Blake2B) dst s

let hash_blake2b_256 input input_len dst = BlB256.blake2b 64ul dst input_len input 0ul (null #MUT uint8)
