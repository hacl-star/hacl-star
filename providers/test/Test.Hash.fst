module Test.Hash

module H = EverCrypt.Hash
module HI = EverCrypt.Hash.Incremental

module ST = FStar.HyperStack.ST
module M = LowStar.Modifies

module MP = LowStar.ModifiesPat

module B = LowStar.Buffer

open LowStar.BufferOps
open Spec.Hash.Definitions
open Spec.Hash.Lemmas

open ST


#set-options "--max_fuel 0 --max_ifuel 0"
let main (): St unit =
  let s1 = H.create SHA2_256 in
  let h1 = ST.get () in
  let s2 = H.create SHA2_384 in
  let h2 = ST.get () in
  H.frame_invariant M.loc_none s1 h1 h2;
  H.init #(Ghost.hide SHA2_256) s1;
  let h3 = ST.get () in
  H.frame_invariant (H.footprint s1 h1) s2 h2 h3;
  H.init #(Ghost.hide SHA2_384) s2

#push-options "--z3rlimit 100"
let test_incremental_api (): St unit =
  // Note: this function cannot be in the Stack effect because it performs some
  // allocations (even though it frees them afterwards).
  push_frame ();
  let b1 = B.alloca_of_list [ 0x00uy; 0x01uy; 0x02uy; 0x04uy ] in
  let b2 = B.alloca_of_list [ 0x05uy; 0x06uy; 0x07uy; 0x08uy ] in

  let st = HI.create_in SHA2_256 HyperStack.root in
  HI.init SHA2_256 st;
  let h0 = ST.get () in
  assert B.(loc_disjoint (HI.footprint h0 st) (loc_buffer b1));
  assert (HI.hashed h0 st `Seq.equal` Seq.empty);

  assert_norm (4 < pow2 61);
  HI.update SHA2_256 st b1 4ul;
  let h1 = ST.get () in
  assert (HI.hashed h1 st `Seq.equal` (Seq.append Seq.empty (B.as_seq h0 b1)));
  Seq.append_empty_l (B.as_seq h0 b1);
  assert (HI.hashed h1 st `Seq.equal` (B.as_seq h0 b1));

  assert (Seq.length (Ghost.reveal (Ghost.hide (B.as_seq h0 b1))) = 4);
  assert_norm (8 < pow2 61);
  HI.update SHA2_256 st b2 4ul;
  let h2 = ST.get () in
  assert (HI.hashed h2 st `Seq.equal` (Seq.append (B.as_seq h0 b1) (B.as_seq h0 b2)));

  // An example of how to call the hash preservation lemma...
  let dst = B.alloca 0uy 32ul in
  let h3 = ST.get () in
  // Auto-framing!
  HI.finish SHA2_256 st dst;

  let h4 = ST.get () in
  assert (Seq.equal (B.as_seq h4 dst)
    (Spec.Hash.hash SHA2_256 (Seq.append (B.as_seq h0 b1) (B.as_seq h0 b2))));

  HI.free SHA2_256 st;
  pop_frame ()
