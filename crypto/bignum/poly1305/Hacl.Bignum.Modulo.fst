module Hacl.Bignum.Modulo

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb

open Hacl.Spec.Bignum.Modulo


let reduce b =
  let b0 = b.(0ul) in
  b.(0ul) <- (five <<^ 2ul) *^ b0


let carry_top_wide b =
  let b2 = b.(2ul) in
  let b0 = b.(0ul) in
  let open Hacl.Bignum.Wide in
  let mask = (wide_one <<^ 42ul) -^ wide_one in
  let b2' = b2 &^ mask in
  let b0' = b0 +^ (five *^ (wide_to_limb (b2 >>^ 42ul))) in
  b.(2ul) <- b2';
  b.(0ul) <- b0'
