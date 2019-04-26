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

open Hacl.Spec.Bignum.Modulo

#set-options "--initial_fuel 0 --max_fuel 0"

inline_for_extraction
let mask_2_42_limb : p:limb{v p = pow2 42 - 1} =
  assert_norm (pow2 64 = 0x10000000000000000); assert_norm(pow2 42 - 1 = 0x3ffffffffff);
  uint64_to_limb 0x3ffffffffffuL

inline_for_extraction let mask_2_42_wide : p:Hacl.Bignum.Wide.t{w p = pow2 42 - 1} =
  limb_to_wide mask_2_42_limb


[@"c_inline"]
val reduce:
  b:felem ->
  Stack unit
  (requires (fun h -> live h b /\ reduce_pre (as_seq h b)))
  (ensures (fun h0 _ h1 -> live h0 b /\ reduce_pre (as_seq h0 b) /\ live h1 b /\ modifies_1 b h0 h1
    /\ as_seq h1 b == reduce_spec (as_seq h0 b)))
[@"c_inline"]
let reduce b =
  assert_norm(pow2 4 = 16);
  assert_norm(pow2 2 = 4);
  let b0 = b.(0ul) in
  Math.Lemmas.modulo_lemma (v b0 * 16) (pow2 64);
  Math.Lemmas.modulo_lemma (v b0 * 4) (pow2 64);
  b.(0ul) <- (b0 <<^ 4ul) +^ (b0 <<^ 2ul)


#set-options "--z3rlimit 20"

[@"c_inline"]
val carry_top:
  b:felem ->
  Stack unit
  (requires (fun h -> live h b /\ carry_top_pre (as_seq h b)))
  (ensures (fun h0 _ h1 -> live h0 b /\ carry_top_pre (as_seq h0 b) /\ live h1 b /\ modifies_1 b h0 h1
    /\ as_seq h1 b == carry_top_spec (as_seq h0 b)))
[@"c_inline"]
let carry_top b =
  let b2 = b.(2ul) in
  let b0 = b.(0ul) in
  assert_norm((1 * pow2 limb_size) % pow2 (word_size) = pow2 (limb_size));
  assert_norm(pow2 limb_size > 1);
  Math.Lemmas.modulo_lemma (v b2 / pow2 42) (pow2 word_size);
  let b2_42 = b2 >>^ 42ul in
  cut (v b2_42 = v b2 / pow2 42);
  assert_norm(pow2 2 = 4); Math.Lemmas.modulo_lemma (v b2_42 * 4) (pow2 64);
  b.(2ul) <- b2 &^ mask_2_42_limb;
  b.(0ul) <- ((b2_42 <<^ 2ul) +^ b2_42) +^ b0


[@"c_inline"]
val carry_top_wide:
  b:felem_wide ->
  Stack unit
    (requires (fun h -> live h b /\ carry_top_wide_pre (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 b /\ carry_top_wide_pre (as_seq h0 b) /\ live h1 b /\ modifies_1 b h0 h1
      /\ as_seq h1 b == carry_top_wide_spec (as_seq h0 b)))
[@"c_inline"]
let carry_top_wide b =
  let b2 = b.(2ul) in
  let b0 = b.(0ul) in
  let open Hacl.Bignum.Wide in
  assert_norm((1 * pow2 limb_size) % pow2 (2 * word_size) = pow2 (limb_size));
  assert_norm(pow2 limb_size > 1);
  let b2' = b2 &^ mask_2_42_wide in
  Math.Lemmas.modulo_lemma (v b2 / pow2 42) (pow2 word_size);
  let b2_42 = wide_to_limb (b2 >>^ 42ul) in
  assert_norm(pow2 2 = 4); Math.Lemmas.modulo_lemma (Hacl.Bignum.Limb.v b2_42 * 4) (pow2 64);
  let b0' = b0 +^ limb_to_wide Hacl.Bignum.Limb.((b2_42 <<^ 2ul) +^ b2_42) in
  b.(2ul) <- b2';
  b.(0ul) <- b0'
