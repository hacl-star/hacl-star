module Hacl.Impl.SHA512.ModQ

open FStar.Buffer
open Hacl.Impl.BignumQ.Mul

val sha512_modq:
  out:qelemB ->
  input:buffer Hacl.UInt8.t ->
  len  :UInt32.t{UInt32.v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 input /\ live h0 out))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h1 out /\ modifies_1 out h0 h1 /\
          Hacl.Spec.BignumQ.Eval.eval_q (as_seq h1 out) == Spec.Ed25519.sha512_modq (as_seq h0 input)))
let sha512_modq out input len =
  push_frame();
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) 10ul in
  push_frame();
  let hash = create (Hacl.Cast.uint8_to_sint8 0uy) 64ul in
  Hacl.Impl.Sha512.sha512 hash input len;
  Hacl.Impl.Load56.load_64_bytes tmp hash;
  pop_frame();
  Hacl.Impl.BignumQ.Mul.barrett_reduction out tmp;
  pop_frame()
