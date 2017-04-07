module Hacl.Impl.Ed25519.RecoverX

open FStar.Buffer
open Hacl.Spec.BignumQ.Eval

let qelemB = b:buffer Hacl.UInt64.t{length b = 5}

val recover_x:
  x:qelemB ->
  y:qelemB{disjoint x y} ->
  sign:Hacl.UInt64.t ->
  Stack FStar.UInt32.t
    (requires (fun h -> live h x /\ live h y))
    (ensures (fun h0 _ h1 -> live h1 x /\ live h0 y /\ modifies_1 x h0 h1))
let recover_x x y sign =
  push_frame();
  let m = create 0uL 5ul in
  let m = Hacl.Impl.BignumQ.Mul.make_m m in
  Hacl.Impl.BignumQ.Mul.subm_conditional x y m;
  let x4 = x.(4ul) in
  let res =
  if FStar.UInt64 (x4 >= 0x10000000000uL) then 1uL
  else (
    // Compute ((y `fmul` y) `fsub` 1) `fmul` (modp_inv ((d `fmul` y `fmul` y) `fadd` one))
    
  )
