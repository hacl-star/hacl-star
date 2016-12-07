module Hacl.Bignum.Modulo

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb

#set-options "--lax"

inline_for_extraction let two54m152 = uint64_to_limb 0x3fffffffffff68uL
inline_for_extraction let two54m8   = uint64_to_limb 0x3ffffffffffff8uL
inline_for_extraction let nineteen  = uint64_to_limb 19uL
inline_for_extraction let mask_51    = uint64_to_limb 0x7ffffffffffffuL

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


let add_zero b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  b.(0ul) <- b0 +^ two54m152;
  b.(1ul) <- b1 +^ two54m8;
  b.(2ul) <- b2 +^ two54m8;
  b.(3ul) <- b3 +^ two54m8;
  b.(4ul) <- b4 +^ two54m8

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

let carry_top b =
  let b4 = b.(4ul) in
  let b0 = b.(0ul) in
  let mask = (limb_one <<^ climb_size) -^ limb_one in
  let nineteen = (limb_one <<^ 4ul) +^ (limb_one <<^ 1ul) +^ limb_one in
  let b4' = b4 &^ mask in
  let b0' = b0 +^ (nineteen *^ (b4 >>^ climb_size)) in
  b.(4ul) <- b4';
  b.(0ul) <- b0'


let reduce_pre s =
  let _ = () in
  v (Seq.index s 0) * 19 < pow2 64


let reduce_spec s =
  let nineteen = (limb_one <<^ 4ul) +^ (limb_one <<^ 1ul) +^ limb_one in
  let s0 = Seq.index s 0 in
  Seq.upd s 0 (s0 *^ nineteen)


let reduce b =
  let nineteen = (limb_one <<^ 4ul) +^ (limb_one <<^ 1ul) +^ limb_one in
  let b0 = b.(0ul) in
  b.(0ul) <- nineteen *^ b0


let reduce_wide_pre s =
  let _ = () in
  w (Seq.index s 0) * 19 < pow2 128


let reduce_wide_spec s =
  let open Hacl.Bignum.Wide in
  let s0 = Seq.index s 0 in
  let s0_19 = (s0 <<^ 4ul) +^ (s0 <<^ 1ul) +^ s0 in
  Seq.upd s 0 (s0_19)


let reduce_wide b =
  let s0 = b.(0ul) in
  let open Hacl.Bignum.Wide in
  let s0_19 = (s0 <<^ 4ul) +^ (s0 <<^ 1ul) +^ s0 in
  b.(0ul) <- s0_19
