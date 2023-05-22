module Test.Hash

module HI = EverCrypt.Hash.Incremental
module S = Hacl.Streaming.Functor

module ST = FStar.HyperStack.ST
module M = LowStar.Modifies

module MP = LowStar.ModifiesPat

module B = LowStar.Buffer
module G = FStar.Ghost

open LowStar.BufferOps
open Spec.Hash.Definitions
open Spec.Hash.Lemmas
open Lib.IntTypes

open FStar.HyperStack.ST


#set-options "--max_fuel 0 --max_ifuel 0"
let main (): St unit =
  // Nothing here: EverCrypt.Hash is no longer a public API, all clients
  // expected to go through HI
  ()

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let test_incremental_api (): St unit =
  // Note: this function cannot be in the Stack effect because it performs some
  // allocations (even though it frees them afterwards).
  push_frame ();
  let b1 = B.alloca_of_list [ u8 0x00; u8 0x01; u8 0x02; u8 0x04 ] in
  let b2 = B.alloca_of_list [ u8 0x05; u8 0x06; u8 0x07; u8 0x08 ] in

  let st = HI.create_in SHA2_256 HyperStack.root in
  HI.init (G.hide SHA2_256) st;
  let h0 = ST.get () in
  assert B.(loc_disjoint (S.footprint HI.evercrypt_hash SHA2_256 h0 st) (loc_buffer b1));
  assert (S.seen HI.evercrypt_hash SHA2_256 h0 st `Seq.equal` Seq.empty);

  assert_norm (4 < pow2 61);
  let EverCrypt.Error.Success = HI.update (G.hide SHA2_256) st b1 4ul in
  let h1 = ST.get () in
  assert (HI.hashed h1 st `Seq.equal` (Seq.append Seq.empty (B.as_seq h0 b1)));
  Seq.append_empty_l (B.as_seq h0 b1);
  assert (HI.hashed h1 st `Seq.equal` (B.as_seq h0 b1));

  assert (Seq.length (Ghost.reveal (Ghost.hide (B.as_seq h0 b1))) = 4);
  assert_norm (8 < pow2 61);
  let EverCrypt.Error.Success = HI.update (G.hide SHA2_256) st b2 4ul in
  let h2 = ST.get () in
  assert (HI.hashed h2 st `Seq.equal` (Seq.append (B.as_seq h0 b1) (B.as_seq h0 b2)));

  // An example of how to call the hash preservation lemma...
  let dst = B.alloca (u8 0) 32ul in
  let h3 = ST.get () in
  // Auto-framing!
  HI.finish (G.hide SHA2_256) st dst ();

  let h4 = ST.get () in
  assert (Seq.equal (B.as_seq h4 dst)
    (Spec.Agile.Hash.hash SHA2_256 (Seq.append (B.as_seq h0 b1) (B.as_seq h0 b2))));

  HI.free (G.hide SHA2_256) st;
  pop_frame ()
