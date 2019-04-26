module Hacl.Impl.SHA512.Ed25519_2

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.UInt32
open FStar.HyperStack
open FStar.Seq
open FStar.Buffer

open Hacl.Impl.SHA2_512

#reset-options "--max_fuel 0 --z3rlimit 20"

let op_String_Access h (b:buffer Hacl.UInt8.t{live h b}) = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)

val hash_block_and_rest:
  out:buffer Hacl.UInt8.t{length out = 64} ->
  block:buffer Hacl.UInt8.t{length block = 128 /\ disjoint block out} ->
  msg:buffer Hacl.UInt8.t{disjoint msg out} ->
  len:UInt32.t{v len = length msg} ->
  Stack unit
    (requires (fun h -> live h out /\ live h block /\ live h msg))
    (ensures (fun h0 _ h1 -> live h0 block /\ live h0 msg /\ live h1 out /\ modifies_1 out h0 h1 /\
      h1.[out] == Spec.SHA2_512.hash (h0.[block] @| h0.[msg])))

#reset-options "--max_fuel 0 --z3rlimit 200"

let hash_block_and_rest out block msg len =
  push_frame();
  let h0 = ST.get() in
  let nblocks = len >>^ 7ul in
  assert_norm(pow2 7 = 128);
  let rest = (len &^ 127ul) in
  UInt.logand_mask (UInt32.v len) 7;
  assert(UInt32.v nblocks = UInt32.v len / 128);
  assert(UInt32.v rest = UInt32.v len % 128);
  let st      = create (Hacl.Cast.uint64_to_sint64 0uL) 169ul in
  let h1 = ST.get() in
  no_upd_lemma_0 h0 h1 block;
  no_upd_lemma_0 h0 h1 msg;
  init st;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 st block;
  no_upd_lemma_1 h1 h2 st msg;
  update st block;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 st msg;
  update_multi st (Buffer.sub msg 0ul (128ul *^ nblocks)) nblocks;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 st msg;
  update_last st (Buffer.offset msg (128ul *^ nblocks)) rest;
  let h5 = ST.get() in
  finish st out;
  let h6 = ST.get() in
  Spec.SHA2_512.(lemma_hash_prepend h_0 (h0.[block]) (h0.[msg]));
  pop_frame()

