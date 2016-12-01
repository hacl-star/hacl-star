module Hacl.Bignum.Limb

open FStar.Mul
open Hacl.Bignum.Parameters
open Hacl.UInt64
open Hacl.Cast

let v x = v x

inline_for_extraction let zero = uint64_to_sint64 0uL
inline_for_extraction let one  = uint64_to_sint64 1uL


(* Addition primitives *)
inline_for_extraction let add a b = add a b
inline_for_extraction let add_mod a b = add_mod a b
(* Subtraction primitives *)
inline_for_extraction let sub a b = sub a b
inline_for_extraction let sub_mod a b = sub_mod a b
(* Multiplication primitives *)
inline_for_extraction let mul a b = mul a b
inline_for_extraction let mul_mod a b = mul_mod a b

(* Bitwise operators *)
inline_for_extraction let logand a b = logand a b
inline_for_extraction let logxor a b = logxor a b
inline_for_extraction let logor  a b = logor  a b
inline_for_extraction let lognot a   = lognot a

(* Shift operators *)
inline_for_extraction let shift_right a s = shift_right a s
inline_for_extraction let shift_left  a s = shift_left a s

inline_for_extraction let eq_mask a b  = eq_mask a b
inline_for_extraction let gte_mask a b = gte_mask a b
inline_for_extraction let gt_mask a b  = gt_mask a b
inline_for_extraction let lt_mask a b  = lt_mask a b
inline_for_extraction let lte_mask a b = lte_mask a b

inline_for_extraction let limb_to_byte x = sint64_to_sint8 x
inline_for_extraction let byte_to_limb x = sint8_to_sint64 x
