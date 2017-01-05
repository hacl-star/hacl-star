module Hacl.Bignum.Fsum

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb


module U32 = FStar.UInt32

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val fsum:
  a:felem -> b:felem ->
  Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> true))
let fsum a b =
  let a0 = a.(0ul) in
  let a1 = a.(1ul) in
  let a2 = a.(2ul) in
  let a3 = a.(3ul) in
  let a4 = a.(4ul) in
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  a.(0ul) <- a0 +%^ b0;
  a.(1ul) <- a1 +%^ b1;
  a.(2ul) <- a2 +%^ b2;
  a.(3ul) <- a3 +%^ b3;
  a.(4ul) <- a4 +%^ b4
