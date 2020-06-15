module Hacl.Bignum.ModInv64

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions
module S = Hacl.Spec.Bignum.Montgomery
module BN = Hacl.Bignum


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val mod_inv_u64: n0:uint64 ->
  Stack uint64
  (requires fun h -> True)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.mod_inv_u64 n0)
