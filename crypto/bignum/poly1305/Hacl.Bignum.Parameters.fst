module Hacl.Bignum.Parameters

open FStar.HyperStack
open FStar.Buffer
open Hacl.Cast

inline_for_extraction let clen = 3ul
inline_for_extraction let climb_size = 44ul

let lemma_prime_limb_size () = assert_norm (pow2 (3 * 44) > pow2 130 - 5)

open Hacl.UInt64

inline_for_extraction let v x = v x

let lemma_limb_injectivity a b = ()

inline_for_extraction let limb_zero = uint64_to_sint64 0uL
inline_for_extraction let limb_one  = uint64_to_sint64 1uL

(* Addition primitives *)
inline_for_extraction let limb_add a b = add a b
inline_for_extraction let limb_add_mod a b = add_mod a b
(* Subtraction primitives *)
inline_for_extraction let limb_sub a b = sub a b
inline_for_extraction let limb_sub_mod a b = sub_mod a b
(* Multiplication primitives *)
inline_for_extraction let limb_mul a b = mul a b
inline_for_extraction let limb_mul_mod a b = mul_mod a b

(* Bitwise operators *)
inline_for_extraction let limb_logand a b = logand a b
inline_for_extraction let limb_logxor a b = logxor a b
inline_for_extraction let limb_logor  a b = logor  a b
inline_for_extraction let limb_lognot a   = lognot a

(* Shift operators *)
inline_for_extraction let limb_shift_right a s = shift_right a s
inline_for_extraction let limb_shift_left  a s = shift_left a s

inline_for_extraction let limb_eq_mask a b  = eq_mask a b
inline_for_extraction let limb_gte_mask a b = gte_mask a b
inline_for_extraction let limb_gt_mask a b  = gt_mask a b
inline_for_extraction let limb_lt_mask a b  = lt_mask a b
inline_for_extraction let limb_lte_mask a b = lte_mask a b

inline_for_extraction let limb_to_byte x = assert_norm(pow2 8 = 256); sint64_to_sint8 x
inline_for_extraction let byte_to_limb x = sint8_to_sint64 x

inline_for_extraction let w x = Hacl.UInt128.v x

let lemma_wide_injectivity a b = ()

inline_for_extraction let wide_zero = sint64_to_sint128 (uint64_to_sint64 0uL)
inline_for_extraction let wide_one  = sint64_to_sint128 (uint64_to_sint64 1uL)

(* Addition primitives *)
inline_for_extraction let wide_add a b = Hacl.UInt128.add a b
inline_for_extraction let wide_add_mod a b = Hacl.UInt128.add_mod a b
(* Subtraction primitives *)
inline_for_extraction let wide_sub a b = Hacl.UInt128.sub a b
inline_for_extraction let wide_sub_mod a b = Hacl.UInt128.sub_mod a b

(* Bitwise operators *)
inline_for_extraction let wide_logand a b = Hacl.UInt128.logand a b
inline_for_extraction let wide_logxor a b = Hacl.UInt128.logxor a b
inline_for_extraction let wide_logor  a b = Hacl.UInt128.logor  a b
inline_for_extraction let wide_lognot a   = Hacl.UInt128.lognot a

(* Shift operators *)
inline_for_extraction let wide_shift_right a s = Hacl.UInt128.shift_right a s
inline_for_extraction let wide_shift_left  a s = Hacl.UInt128.shift_left a s

inline_for_extraction let wide_eq_mask a b  = Hacl.UInt128.eq_mask a b
inline_for_extraction let wide_gte_mask a b = Hacl.UInt128.gte_mask a b
inline_for_extraction let wide_gt_mask a b  = Hacl.UInt128.gt_mask a b
inline_for_extraction let wide_lt_mask a b  = Hacl.UInt128.lt_mask a b
inline_for_extraction let wide_lte_mask a b = Hacl.UInt128.lte_mask a b

inline_for_extraction let mul_wide x y = Hacl.UInt128.mul_wide x y

inline_for_extraction let limb_to_wide x = sint64_to_sint128 x
inline_for_extraction let wide_to_limb x = sint128_to_sint64 x

inline_for_extraction let uint64_to_limb x = Hacl.Cast.uint64_to_sint64 x
