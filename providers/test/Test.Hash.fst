module Test.Hash

module HI = EverCrypt.Hash.Incremental
module S = Hacl.Streaming.Functor

module ST = FStar.HyperStack.ST


module B = LowStar.Buffer
module G = FStar.Ghost

open LowStar.BufferOps
open Spec.Hash.Definitions
open Spec.Hash.Lemmas
open Lib.IntTypes

open FStar.HyperStack.ST


#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let test_incremental_api (): ST unit
  (requires fun _ -> True)
  (ensures fun h0 _ h1 -> True) =
  // Note: this function cannot be in the Stack effect because it performs some
  // allocations (even though it frees them afterwards).
  let h00 = ST.get () in
  push_frame ();
  let b1 = B.alloca_of_list [ u8 0x00; u8 0x01; u8 0x02; u8 0x04 ] in
  let b2 = B.alloca_of_list [ u8 0x05; u8 0x06; u8 0x07; u8 0x08 ] in

  let st = HI.malloc SHA2_256 HyperStack.root in
  if B.is_null st then begin
    pop_frame ();
    LowStar.Failure.failwith "OUT OF MEMORY"
  end else
    HI.reset (G.hide SHA2_256) st ();
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
    assert B.(fresh_loc (loc_buffer dst) h2 h3);
    B.modifies_only_not_unused_in B.loc_none h2 h3;
    assert B.(modifies (loc_none) h2 h3);
    // Auto-framing no longer works OH NOES
    S.frame_invariant HI.evercrypt_hash SHA2_256 B.loc_none st h2 h3;
    assert B.(loc_disjoint (loc_buffer dst) (S.footprint HI.evercrypt_hash SHA2_256 h3 st));
    HI.digest (G.hide SHA2_256) st dst ();

    let h4 = ST.get () in
    assert (Seq.equal (B.as_seq h4 dst)
      (Spec.Agile.Hash.hash SHA2_256 (Seq.append (B.as_seq h0 b1) (B.as_seq h0 b2))));

    HI.free (G.hide SHA2_256) st;
    pop_frame ();
    let h5 = ST.get () in
    ()

#set-options "--fuel 0 --ifuel 0"
let main (): St unit =
  // Nothing here: EverCrypt.Hash is no longer a public API, all clients
  // expected to go through HI
  test_incremental_api ()
