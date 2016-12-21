module Hacl.Bignum.Crecip


open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb

module U32 = FStar.UInt32

val crecip:
  out:felem ->
  z:felem -> Stack unit
  (requires (fun h -> live h out /\ live h z))
  (ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1))
