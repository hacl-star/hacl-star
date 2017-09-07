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

inline_for_extraction let two54m152 : x:limb{v x = 0x3fffffffffff68} =
  assert_norm (pow2 64 > 0x3fffffffffff68); uint64_to_limb 0x3fffffffffff68uL
inline_for_extraction let two54m8 : x:limb{v x = 0x3ffffffffffff8} =
  assert_norm (pow2 64 > 0x3ffffffffffff8); uint64_to_limb 0x3ffffffffffff8uL
inline_for_extraction let nineteen : x:limb{v x = 19} = assert_norm(19 < pow2 64); uint64_to_limb 19uL

#set-options "--z3rlimit 20"

[@"substitute"]
private val add_zero_:
  b:felem ->
  Stack unit
    (requires (fun h -> live h b /\ add_zero_pre (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 b /\ add_zero_pre (as_seq h0 b) /\ live h1 b /\ modifies_1 b h0 h1
      /\ as_seq h1 b == add_zero_spec (as_seq h0 b)))
[@"substitute"]
private let add_zero_ b =
  assert_norm (pow2 63 > 0x3fffffffffff68);
  assert_norm (pow2 63 > 0x3ffffffffffff8);
  Math.Lemmas.pow2_double_sum 63;
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


[@"substitute"]
val add_zero:
  b:felem ->
  Stack unit
    (requires (fun h -> live h b /\ add_zero_pre (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 b /\ add_zero_pre (as_seq h0 b) /\ live h1 b /\ modifies_1 b h0 h1
      /\ as_seq h1 b == add_zero_spec (as_seq h0 b)
      /\ eval h1 b % prime = eval h0 b % prime))
[@"substitute"]
let add_zero b =
  let h0 = ST.get() in
  add_zero_ b;
  lemma_add_zero_spec (as_seq h0 b)


val carry_top:
  b:felem ->
  Stack unit
  (requires (fun h -> live h b /\ carry_top_pre (as_seq h b)))
  (ensures (fun h0 _ h1 -> live h0 b /\ carry_top_pre (as_seq h0 b) /\ live h1 b /\ modifies_1 b h0 h1
    /\ as_seq h1 b == carry_top_spec (as_seq h0 b)))
let carry_top b =
  let b4 = b.(4ul) in
  let b0 = b.(0ul) in
  assert_norm((1 * pow2 limb_size) % pow2 word_size = pow2 limb_size);
  assert_norm(pow2 limb_size > 1);
  let b4' = b4 &^ mask_51 in
  let b0' = b0 +^ (nineteen *^ (b4 >>^ climb_size)) in
  b.(4ul) <- b4';
  b.(0ul) <- b0'


[@"substitute"]
val reduce:
  b:felem ->
  Stack unit
  (requires (fun h -> live h b /\ reduce_pre (as_seq h b)))
  (ensures (fun h0 _ h1 -> live h0 b /\ reduce_pre (as_seq h0 b) /\ live h1 b /\ modifies_1 b h0 h1
    /\ as_seq h1 b == reduce_spec (as_seq h0 b)))
[@"substitute"]
let reduce b =
  let b0 = b.(0ul) in
  b.(0ul) <- nineteen *^ b0


[@"substitute"]
val carry_top_wide:
  b:felem_wide ->
  Stack unit
    (requires (fun h -> live h b /\ carry_top_wide_pre (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 b /\ carry_top_wide_pre (as_seq h0 b) /\ live h1 b /\ modifies_1 b h0 h1
      /\ as_seq h1 b == carry_top_wide_spec (as_seq h0 b)))
[@"substitute"]
let carry_top_wide b =
  let b4 = b.(4ul) in
  let b0 = b.(0ul) in
  let open Hacl.Bignum.Wide in
  assert_norm((1 * pow2 limb_size) % pow2 (2 * word_size) = pow2 (limb_size));
  assert_norm(pow2 limb_size > 1);
  let b4' = b4 &^ mask_51_wide in
  Math.Lemmas.modulo_lemma (w b4 / pow2 limb_size) (pow2 word_size);
  let b0' = b0 +^ (nineteen *^ (wide_to_limb (b4 >>^ climb_size))) in
  b.(4ul) <- b4';
  b.(0ul) <- b0'
