module Hacl.EC.Curve25519.Bignum

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Ghost
open Hacl.UInt64

open FStar.Buffer
open FStar.Math.Lib
open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint
open Hacl.EC.Curve25519.Utils

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"


(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64
module H128  = Hacl.UInt128


val copy_bigint: output:bigint -> input:bigint{disjoint input output} -> Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let copy_bigint output i =
  let i0 = i.(0ul) in
  let i1 = i.(1ul) in
  let i2 = i.(2ul) in
  let i3 = i.(3ul) in
  let i4 = i.(4ul) in
  update_5 output i0 i1 i2 i3 i4


val copy_to_bigint': output:bigint -> input:bigint_wide{disjoint input output} -> Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let rec copy_to_bigint' output b =
  Math.Lemmas.pow2_lt_compat 128 64;
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let open Hacl.UInt128 in
  update_5 output (Hacl.Cast.sint128_to_sint64 b0)
                 (Hacl.Cast.sint128_to_sint64 b1)
                 (Hacl.Cast.sint128_to_sint64 b2)
                 (Hacl.Cast.sint128_to_sint64 b3)
                 (Hacl.Cast.sint128_to_sint64 b4)


val copy_to_bigint:
  output:bigint ->
  input:bigint_wide{disjoint input output} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures (fun h0 _ h1 -> modifies_1 output h0 h1 /\ live h1 output))
let copy_to_bigint output b =
  copy_to_bigint' output b


val copy_to_bigint_wide': output:bigint_wide -> input:bigint{disjoint input output} -> Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let rec copy_to_bigint_wide' output b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  update_wide_5 output (Hacl.Cast.sint64_to_sint128 b0)
                      (Hacl.Cast.sint64_to_sint128 b1)
                      (Hacl.Cast.sint64_to_sint128 b2)
                      (Hacl.Cast.sint64_to_sint128 b3)
                      (Hacl.Cast.sint64_to_sint128 b4)


val copy_to_bigint_wide: output:bigint_wide -> input:bigint{disjoint input output} -> Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let copy_to_bigint_wide output b =
  copy_to_bigint_wide' output b


val modulo:
  output:bigint ->
  input:bigint_wide{disjoint input output} ->
  Stack unit
    (requires (fun h -> live h input /\ live h output /\ length input >= 2*norm_length - 1 ))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h1 input /\ modifies_2 output input h0 h1))
let modulo output b =
  Hacl.EC.Curve25519.Bignum.Modulo.freduce_degree b;
  Hacl.EC.Curve25519.Bignum.Modulo.freduce_coefficients_wide b;
  copy_to_bigint output b


val fsum: a:bigint{length a >= norm_length + 1} -> b:bigint{disjoint a b} -> Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1))
let fsum a b =
  Hacl.EC.Curve25519.Bignum.Fsum.fsum' a b;
  Hacl.EC.Curve25519.Bignum.Modulo.freduce_coefficients a


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val fdifference: a:bigint{length a >= norm_length+1} -> b:bigint{disjoint a b} -> Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1))
let fdifference a b =
  push_frame ();
  let b' = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  copy_bigint b' b;
  Hacl.EC.Curve25519.Bignum.Fdifference.add_big_zero b';
  Hacl.EC.Curve25519.Bignum.Fdifference.fdifference' a b';
  Hacl.EC.Curve25519.Bignum.Modulo.freduce_coefficients a;
  pop_frame()


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val fscalar:
    res:bigint -> b:bigint{disjoint res b} -> s:s64 -> Stack unit
  (requires (fun h -> live h res /\ live h b))
  (ensures (fun h0 _ h1 -> live h1 res /\ modifies_1 res h0 h1))
let fscalar res b s =
  push_frame ();
  let tmp = create (Hacl.Cast.uint64_to_sint128 0uL) (6ul) in
  Hacl.EC.Curve25519.Bignum.Fscalar.scalar' tmp b s;
  Hacl.EC.Curve25519.Bignum.Modulo.freduce_coefficients_wide tmp;
  copy_to_bigint res tmp;
  pop_frame()


val fmul: res:bigint -> a:bigint{disjoint res a} -> b:bigint{disjoint res b} -> Stack unit
    (requires (fun h -> live h res /\ live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h1 res /\ modifies_1 res h0 h1))
let fmul res a b =
  push_frame ();
  let tmp = create (Hacl.Cast.uint64_to_sint128 0uL) 9ul in
  Hacl.EC.Curve25519.Bignum.Fproduct.multiplication tmp a b;
  modulo res tmp;
  pop_frame()


val fsquare: res:bigint -> a:bigint{disjoint res a} -> Stack unit
    (requires (fun h -> live h res /\ live h a))
    (ensures (fun h0 _ h1 -> live h1 res /\ modifies_1 res h0 h1))
let fsquare res a =
  fmul res a a
