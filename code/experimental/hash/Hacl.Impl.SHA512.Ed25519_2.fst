module Hacl.Impl.SHA512.Ed25519_2

open FStar.Mul
open FStar.UInt32
open FStar.HyperStack
open FStar.Seq
open FStar.Buffer

open Hacl.Hash.SHA2_512

#reset-options "--max_fuel 0 --z3rlimit 20"


val hash_block_and_rest:
  out:buffer Hacl.UInt8.t{length out = 64} ->
  block:buffer Hacl.UInt8.t{length block = 128 /\ disjoint block out} ->
  msg:buffer Hacl.UInt8.t{disjoint msg out} ->
  len:UInt32.t{v len = length msg} ->
  Stack unit
    (requires (fun h -> live h out /\ live h block /\ live h msg))
    (ensures (fun h0 _ h1 -> live h0 block /\ live h0 msg /\ live h1 out /\ modifies_1 out h0 h1 /\
      as_seq h1 out == Spec.SHA2_512.hash (as_seq h0 block @| as_seq h0 msg)))

#set-options "--lax"

let hash_block_and_rest out block msg len =
  push_frame();
  let nblocks = len >>^ 7ul in
  let rest    = Int.Cast.uint32_to_uint64 (len &^ 127ul) in
  let st      = create 0uL 169ul in
  init st;
  update st block;
  update_multi st (Buffer.sub msg 0ul (128ul *^ nblocks)) nblocks;
  update_last st (Buffer.offset msg (128ul *^ nblocks)) rest;
  finish st out;
  pop_frame()
