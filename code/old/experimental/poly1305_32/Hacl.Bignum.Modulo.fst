module Hacl.Bignum.Modulo

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb

(* open Hacl.Spec.Bignum.Modulo *)

#reset-options "--initial_fuel 0 --max_fuel 0"

inline_for_extraction let mask_2_26 : p:Hacl.Bignum.Wide.t{w p = pow2 26 - 1} =
  assert_norm (pow2 32 = 0x100000000); assert_norm(pow2 26 - 1 = 0x3ffffff);
  limb_to_wide (uint32_to_limb 0x3fffffful)


inline_for_extraction let mask_2_26' : p:Hacl.Bignum.Limb.t{v p = pow2 26 - 1} =
  assert_norm (pow2 32 = 0x100000000); assert_norm(pow2 26 - 1 = 0x3ffffff);
  uint32_to_limb 0x3fffffful


val reduce:
  b:felem ->
  Stack unit
  (requires (fun h -> live h b (* /\ reduce_pre (as_seq h b) *)))
  (ensures (fun h0 _ h1 -> live h0 b (* /\ reduce_pre (as_seq h0 b) *) /\ live h1 b /\ modifies_1 b h0 h1
    (* /\ as_seq h1 b == reduce_spec (as_seq h0 b) *)))
let reduce b =
  assert_norm(pow2 4 = 16);
  assert_norm(pow2 2 = 4);
  let b0 = b.(0ul) in
  Math.Lemmas.modulo_lemma (v b0 * 16) (pow2 64);
  Math.Lemmas.modulo_lemma (v b0 * 4) (pow2 64);
  b.(0ul) <- (b0 <<^ 2ul) +^ b0


#set-options "--z3rlimit 20"

val carry_top:
  b:felem ->
  Stack unit
  (requires (fun h -> live h b (* /\ carry_top_pre (as_seq h b) *)))
  (ensures (fun h0 _ h1 -> live h0 b (* /\ carry_top_pre (as_seq h0 b) *) /\ live h1 b /\ modifies_1 b h0 h1
    (* /\ as_seq h1 b == carry_top_spec (as_seq h0 b) *)))
let carry_top b =
  let b4 = b.(4ul) in
  let b0 = b.(0ul) in
  assert_norm((1 * pow2 limb_size) % pow2 (word_size) = pow2 (limb_size));
  assert_norm(pow2 limb_size > 1);
  Math.Lemmas.modulo_lemma (v b4 / pow2 26) (pow2 word_size);
  let b4_26 = b4 >>^ 26ul in
  cut (v b4_26 = v b4 / pow2 26);
  assert_norm(pow2 2 = 4); Math.Lemmas.modulo_lemma (v b4_26 * 4) (pow2 64);
  b.(4ul) <- b4 &^ mask_2_26';
  b.(0ul) <- ((b4_26 <<^ 2ul) +^ b4_26) +^ b0


val carry_top_wide:
  b:felem_wide ->
  Stack unit
    (requires (fun h -> live h b (* /\ carry_top_wide_pre (as_seq h b) *)))
    (ensures (fun h0 _ h1 -> live h0 b (* /\ carry_top_wide_pre (as_seq h0 b) *) /\ live h1 b /\ modifies_1 b h0 h1
      (* /\ as_seq h1 b == carry_top_wide_spec (as_seq h0 b) *)
    ))
let carry_top_wide b =
  let b4 = b.(4ul) in
  let b0 = b.(0ul) in
  let open Hacl.Bignum.Wide in
  (* assert_norm((1 * pow2 limb_size) % pow2 (2 * word_size) = pow2 (limb_size)); *)
  (* assert_norm(pow2 limb_size > 1); *)
  let b4' = b4 &^ mask_2_26 in
  (* Math.Lemmas.modulo_lemma (v b2 / pow2 42) (pow2 word_size); *)
  let b4_26 = wide_to_limb (b4 >>^ 26ul) in
  (* assert_norm(pow2 2 = 4); Math.Lemmas.modulo_lemma (Hacl.Bignum.Limb.v b2_42 * 4) (pow2 64); *)
  let b0' = b0 +^ limb_to_wide Hacl.Bignum.Limb.((b4_26 <<^ 2ul) +^ b4_26) in
  b.(4ul) <- b4';
  b.(0ul) <- b0'
