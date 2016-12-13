module Hacl.Bignum.Modulo.Spec

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb


inline_for_extraction let two54m152 =
  assert_norm (pow2 64 > 0x3fffffffffff68); uint64_to_limb 0x3fffffffffff68uL
inline_for_extraction let two54m8   =
  assert_norm (pow2 64 > 0x3ffffffffffff8); uint64_to_limb 0x3ffffffffffff8uL
inline_for_extraction let nineteen  = assert_norm(19 < pow2 64); uint64_to_limb 19uL
inline_for_extraction let mask_51    =
  assert_norm (0x7ffffffffffff < pow2 64);uint64_to_limb 0x7ffffffffffffuL


let add_zero_pre s =
  let _ = () in
  v (Seq.index s 0) < pow2 63
  /\ v (Seq.index s 1) < pow2 63
  /\ v (Seq.index s 2) < pow2 63
  /\ v (Seq.index s 3) < pow2 63
  /\ v (Seq.index s 4) < pow2 63


let add_zero_spec s =
  let s = Seq.upd s 0 (Seq.index s 0 +^ two54m152) in
  let s = Seq.upd s 1 (Seq.index s 1 +^ two54m8) in
  let s = Seq.upd s 2 (Seq.index s 2 +^ two54m8) in
  let s = Seq.upd s 3 (Seq.index s 3 +^ two54m8) in
  Seq.upd s 4 (Seq.index s 4 +^ two54m8)


let carry_top_pre s =
  let _ = () in
  19 * v (Seq.index s 4) + v (Seq.index s 0) < pow2 64


let carry_top_spec s =
  let s4 = Seq.index s 4 in
  let s0 = Seq.index s 0 in
  let mask = (limb_one <<^ climb_size) -^ limb_one in
  let nineteen = (limb_one <<^ 4ul) +^ (limb_one <<^ 1ul) +^ limb_one in
  let s4' = s4 &^ mask in
  let s0' = s0 +^ (nineteen *^ (s4 >>^ climb_size)) in
  let s = Seq.upd s 4 s4' in
  Seq.upd s 0 s0'


let reduce_pre s =
  let _ = () in
  v (Seq.index s 0) * 19 < pow2 64


let reduce_spec s =
  let nineteen = (limb_one <<^ 4ul) +^ (limb_one <<^ 1ul) +^ limb_one in
  let s0 = Seq.index s 0 in
  Seq.upd s 0 (s0 *^ nineteen)


let carry_top_wide_pre s =
  let _ = () in
  w (Seq.index s 4) / pow2 51 < pow2 64
  /\ w (Seq.index s 4) * 19 + w (Seq.index s 0) < pow2 128


let carry_top_wide_spec s =
  let b4 = Seq.index s 4 in
  let b0 = Seq.index s 0 in
  let open Hacl.Bignum.Wide in
  (* TODO: a "mk_mask_wide" function *)
  let mask = (wide_one <<^ climb_size) -^ wide_one in
  let b4' = b4 &^ mask in
  let b0' = b0 +^ (nineteen *^ (wide_to_limb (b4 >>^ climb_size))) in
  let s' = Seq.upd s 4 b4' in
  Seq.upd s' 0 b0'
