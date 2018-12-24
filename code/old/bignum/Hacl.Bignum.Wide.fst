module Hacl.Bignum.Wide

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open Hacl.Bignum.Parameters


let n = wide_n

type t = wide

let v (x:t) : GTot (FStar.UInt.uint_t n) = w x

inline_for_extraction val add: a:t -> b:t{UInt.size (v a + v b) n} -> Tot (c:t{v a + v b = v c})
inline_for_extraction let add a b = wide_add a b

inline_for_extraction val add_mod: a:t -> b:t -> Tot (c:t{(v a + v b) % pow2 n = v c})
inline_for_extraction let add_mod a b = wide_add_mod a b

(* Subtraction primitives *)
inline_for_extraction val sub: a:t -> b:t{(UInt.size (v a - v b) n)} -> Tot (c:t{v a - v b = v c})
inline_for_extraction let sub a b = wide_sub a b

inline_for_extraction val sub_mod: a:t -> b:t -> Tot (c:t{(v a - v b) % pow2 n = v c})
inline_for_extraction let sub_mod a b = wide_sub_mod a b

(* Bitwise operators *)
inline_for_extraction val logand: t -> t -> Tot t
inline_for_extraction let logand a b = wide_logand a b
inline_for_extraction val logxor: t -> t -> Tot t
inline_for_extraction let logxor a b = wide_logxor a b
inline_for_extraction val logor: t -> t -> Tot t
inline_for_extraction let logor a b = wide_logor a b
inline_for_extraction val lognot: t -> Tot t
inline_for_extraction let lognot a = wide_lognot a

(* Shift operators *)
inline_for_extraction val shift_right: a:t -> s:FStar.UInt32.t{FStar.UInt32.v s < n} ->
  Tot (c:t{v c = (v a / (pow2 (FStar.UInt32.v s)))})
inline_for_extraction let shift_right a s = wide_shift_right a s

inline_for_extraction val shift_left: a:t -> s:FStar.UInt32.t{FStar.UInt32.v s < n} ->
  Tot (c:t{v c = ((v a * pow2 (FStar.UInt32.v s)) % pow2 n)})
inline_for_extraction let shift_left a s = wide_shift_left a s

inline_for_extraction val eq_mask: a:t -> b:t -> Tot (c:t{(v a = v b ==> v c = pow2 n - 1) /\ (v a <> v b ==> v c = 0)})
inline_for_extraction let eq_mask a b = wide_eq_mask a b
inline_for_extraction val gte_mask: a:t -> b:t -> Tot (c:t{(v a >= v b ==> v c = pow2 n - 1) /\ (v a < v b ==> v c = 0)})
inline_for_extraction let gte_mask a b = wide_gte_mask a b
inline_for_extraction val gt_mask: a:t -> b:t -> Tot (c:t{(v a > v b ==> v c = pow2 n - 1) /\ (v a <= v b ==> v c = 0)})
inline_for_extraction let gt_mask a b = wide_gt_mask a b
inline_for_extraction val lt_mask: a:t -> b:t -> Tot (c:t{(v a < v b ==> v c = pow2 n - 1) /\ (v a >= v b ==> v c = 0)})
inline_for_extraction let lt_mask a b = wide_lt_mask a b
inline_for_extraction val lte_mask: a:t -> b:t -> Tot (c:t{(v a <= v b ==> v c = pow2 n - 1) /\ (v a > v b ==> v c = 0)})
inline_for_extraction let lte_mask a b = wide_lte_mask a b


(* Infix notations *)
inline_for_extraction let op_Plus_Hat a b = add a b
inline_for_extraction let op_Plus_Percent_Hat a b = add_mod a b
inline_for_extraction let op_Subtraction_Hat a b = sub a b
inline_for_extraction let op_Subtraction_Percent_Hat a b = sub_mod a b
inline_for_extraction let op_Amp_Hat a b = logand a b
inline_for_extraction let op_Hat_Hat a b = logxor a b
inline_for_extraction let op_Bar_Hat a b = logor a b

inline_for_extraction val op_Greater_Greater_Hat: a:t -> s:FStar.UInt32.t{FStar.UInt32.v s < n} ->
  Tot (c:t{v c = (v a / (pow2 (FStar.UInt32.v s)))})
inline_for_extraction let op_Greater_Greater_Hat a s = shift_right a s

inline_for_extraction val op_Less_Less_Hat: a:t -> s:FStar.UInt32.t{FStar.UInt32.v s < n} ->
  Tot (c:t{v c = ((v a * pow2 (FStar.UInt32.v s)) % pow2 n)})
inline_for_extraction let op_Less_Less_Hat a s = shift_left a s

inline_for_extraction let mul_wide a b = mul_wide a b
inline_for_extraction let op_Star_Hat a b = mul_wide a b
