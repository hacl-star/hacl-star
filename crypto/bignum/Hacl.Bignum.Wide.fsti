module Hacl.Bignum.Wide

open FStar.Mul
open Hacl.Bignum.Parameters

inline_for_extraction let n = 2 * word_size

type t = wide

val v: t -> GTot nat

inline_for_extraction val zero: x:t{v x = 0}
inline_for_extraction val one: x:t{v x = 1}

(* Addition primitives *)
inline_for_extraction val add: a:t -> b:t{UInt.size (v a + v b) n} -> Tot (c:t{v a + v b = v c})
inline_for_extraction val add_mod: a:t -> b:t -> Tot (c:t{(v a + v b) % pow2 n = v c})
(* Subtraction primitives *)
inline_for_extraction val sub: a:t -> b:t{UInt.size (v a - v b) n} -> Tot (c:t{UInt.size (v a - v b) n})
inline_for_extraction val sub_mod: a:t -> b:t -> Tot (c:t{(v a - v b) % pow2 n = v c})
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
inline_for_extraction let op_Hat_Hat = logxor
inline_for_extraction let op_Amp_Hat = logand
inline_for_extraction let op_Bar_Hat = logor
inline_for_extraction let op_Less_Less_Hat = shift_left
inline_for_extraction let op_Greater_Greater_Hat = shift_right

inline_for_extraction val mul_wide: a:Hacl.UInt64.t -> b:Hacl.UInt64.t -> Pure t
  (requires True)
  (ensures (fun c -> v c = Hacl.UInt64.v a * Hacl.UInt64.v b))

inline_for_extraction let op_Star_Hat = mul_wide

inline_for_extraction val limb_to_wide: x:Hacl.Bignum.Limb.t -> Tot (y:t{v y = Hacl.Bignum.Limb.v x})
inline_for_extraction val wide_to_limb: x:t -> Tot (y:Hacl.Bignum.Limb.t{Hacl.Bignum.Limb.v y = v x % pow2 Hacl.Bignum.Limb.n})
