module Hacl.Bignum.Crecip

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Crecip

module U32 = FStar.UInt32


val crecip:
  out:felem ->
  z:felem -> Stack unit
  (requires (fun h -> live h out /\ live h z /\ crecip_pre (as_seq h z)))
  (ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1 /\ live h0 z
    /\ crecip_pre (as_seq h0 z)
    /\ as_seq h1 out == crecip_tot (as_seq h0 z)
  ))
