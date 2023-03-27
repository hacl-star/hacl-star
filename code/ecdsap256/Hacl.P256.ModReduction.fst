module Hacl.P256.ModReduction

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field
open Hacl.Impl.P256.SolinasReduction

module S = Spec.P256

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val mul_mod_solinas (x y res:felem) : Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.prime /\ as_nat h y < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == as_nat h0 x * as_nat h0 y % S.prime)

let mul_mod_solinas x y res =
  push_frame ();
  let tmp = create 8ul (u64 0) in
  let h0 = ST.get () in
  bn_mul4 tmp x y;
  let h1 = ST.get () in
  assert (wide_as_nat h1 tmp == as_nat h0 x * as_nat h0 y);
  solinas_reduction_impl tmp res;
  let h2 = ST.get () in
  assert (as_nat h2 res == wide_as_nat h1 tmp % S.prime);
  pop_frame ()


val mul_mod_mont (x y res:felem) : Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.prime /\ as_nat h y < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    fmont_as_nat h1 res == fmont_as_nat h0 x * fmont_as_nat h0 y % S.prime)

let mul_mod_mont x y res = fmul res x y
