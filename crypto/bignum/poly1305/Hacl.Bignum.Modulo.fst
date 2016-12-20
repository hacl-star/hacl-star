module Hacl.Bignum.Modulo

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb

open Hacl.Spec.Bignum.Modulo


let add_zero b = admit()
  (* let b0 = b.(0ul) in *)
  (* let b1 = b.(1ul) in *)
  (* let b2 = b.(2ul) in *)
  (* let b3 = b.(3ul) in *)
  (* let b4 = b.(4ul) in *)
  (* b.(0ul) <- b0 +^ two54m152; *)
  (* b.(1ul) <- b1 +^ two54m8; *)
  (* b.(2ul) <- b2 +^ two54m8; *)
  (* b.(3ul) <- b3 +^ two54m8; *)
  (* b.(4ul) <- b4 +^ two54m8 *)

let carry_top b = admit()
  (* let b4 = b.(4ul) in *)
  (* let b0 = b.(0ul) in *)
  (* let mask = (limb_one <<^ climb_size) -^ limb_one in *)
  (* let nineteen = (limb_one <<^ 4ul) +^ (limb_one <<^ 1ul) +^ limb_one in *)
  (* let b4' = b4 &^ mask in *)
  (* let b0' = b0 +^ (nineteen *^ (b4 >>^ climb_size)) in *)
  (* b.(4ul) <- b4'; *)
  (* b.(0ul) <- b0' *)


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
