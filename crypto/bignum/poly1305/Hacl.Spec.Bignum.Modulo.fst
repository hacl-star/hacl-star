module Hacl.Spec.Bignum.Modulo

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb


inline_for_extraction let mask_2_44 = uint64_to_limb 0xfffffffffffuL
inline_for_extraction let mask_2_42 = uint64_to_limb 0x3ffffffffffuL
inline_for_extraction let five     = uint64_to_limb 5uL

let add_zero_pre s =
  let _ = () in admit()


let add_zero_spec s = admit()


let lemma_add_zero_spec s = admit()


let carry_top_pre s = admit()


let carry_top_spec s = admit()


let lemma_carry_top_spec s = admit()


let reduce_pre s =
  let _ = () in
  v (Seq.index s 0) * 5 < pow2 64


let reduce_spec s =
  let s0 = Seq.index s 0 in
  Seq.upd s 0 (s0 *^ five)


let lemma_reduce_spec s = admit()



let carry_top_wide_pre s =
  let _ = () in admit()


let carry_top_wide_spec s =
  let b2 = Seq.index s 2 in
  let b0 = Seq.index s 0 in
  let open Hacl.Bignum.Wide in
  let mask = (wide_one <<^ 42ul) -^ wide_one in
  let b2' = b2 &^ mask in
  let b0' = b0 +^ (five *^ (wide_to_limb (b2 >>^ 42ul))) in
  let s' = Seq.upd s 2 b2' in
  Seq.upd s' 0 b0'


let lemma_carry_top_wide_spec s = admit()
