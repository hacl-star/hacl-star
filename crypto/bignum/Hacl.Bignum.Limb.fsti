module Hacl.Bignum.Limb

open FStar.Mul
open Hacl.Bignum.Parameters

inline_for_extraction let n = word_size

inline_for_extraction let t = limb

val v: t -> GTot nat

inline_for_extraction val zero: x:t{v x = 0}
inline_for_extraction val one: x:t{v x = 1}


(* Addition primitives *)
inline_for_extraction val add: a:t -> b:t{UInt.size (v a + v b) n} -> Tot (c:t{v a + v b = v c})
inline_for_extraction val add_mod: a:t -> b:t -> Tot (c:t{(v a + v b) % pow2 n = v c})
(* Subtraction primitives *)
inline_for_extraction val sub: a:t -> b:t{UInt.size (v a - v b) n} -> Tot (c:t{UInt.size (v a - v b) n})
inline_for_extraction val sub_mod: a:t -> b:t -> Tot (c:t{(v a - v b) % pow2 n = v c})
(* Multiplication primitives *)
inline_for_extraction val mul: a:t -> b:t{UInt.size (v a * v b) n} -> Tot (c:t{v a * v b = v c})
inline_for_extraction val mul_mod: a:t -> b:t -> Tot (c:t{(v a * v b) % pow2 n = v c})

(* Bitwise operators *)
inline_for_extraction val logand: t -> t -> Tot t
inline_for_extraction val logxor: t -> t -> Tot t
inline_for_extraction val logor: t -> t -> Tot t
inline_for_extraction val lognot: t -> Tot t

(* Shift operators *)
inline_for_extraction val shift_right: a:t -> s:FStar.UInt32.t -> Tot (c:t{FStar.UInt32.v s < n ==> v c = (v a / (pow2 (FStar.UInt32.v s)))})
inline_for_extraction val shift_left: a:t -> s:FStar.UInt32.t -> Tot (c:t{FStar.UInt32.v s < n ==> v c = ((v a * pow2 (FStar.UInt32.v s)) % pow2 n)})

inline_for_extraction val eq_mask: a:t -> b:t -> Tot (c:t{(v a = v b ==> v c = pow2 n - 1) /\ (v a <> v b ==> v c = 0)})
inline_for_extraction val gte_mask: a:t -> b:t -> Tot (c:t{(v a >= v b ==> v c = pow2 n - 1) /\ (v a < v b ==> v c = 0)})
inline_for_extraction val gt_mask: a:t -> b:t -> Tot (c:t{(v a > v b ==> v c = pow2 n - 1) /\ (v a <= v b ==> v c = 0)})
inline_for_extraction val lt_mask: a:t -> b:t -> Tot (c:t{(v a < v b ==> v c = pow2 n - 1) /\ (v a >= v b ==> v c = 0)})
inline_for_extraction val lte_mask: a:t -> b:t -> Tot (c:t{(v a <= v b ==> v c = pow2 n - 1) /\ (v a > v b ==> v c = 0)})

(* Infix notations *)
inline_for_extraction let op_Plus_Hat = add
inline_for_extraction let op_Plus_Percent_Hat = add_mod
inline_for_extraction let op_Subtraction_Hat = sub
inline_for_extraction let op_Subtraction_Percent_Hat = sub_mod
inline_for_extraction let op_Star_Hat = mul
inline_for_extraction let op_Star_Percent_Hat = mul_mod
inline_for_extraction let op_Hat_Hat = logxor
inline_for_extraction let op_Amp_Hat = logand
inline_for_extraction let op_Bar_Hat = logor
inline_for_extraction let op_Less_Less_Hat = shift_left
inline_for_extraction let op_Greater_Greater_Hat = shift_right

inline_for_extraction val limb_to_byte: x:t -> Tot (y:Hacl.UInt8.t{Hacl.UInt8.v y = v x % 256})
inline_for_extraction val byte_to_limb: x:Hacl.UInt8.t -> Tot (y:t{Hacl.UInt8.v x = v y})
