module Hacl.UInt32

open FStar.UInt32

module U32 = FStar.UInt32

assume MaxUint32: pow2 32 = 4294967296

private type _t = U32.t
type t = _t

let n = n

let v (a:t) : GTot int = v a
let add = add
let add_underspec = add_underspec
let add_mod = add_mod
let sub = sub
let sub_underspec = sub_underspec
let sub_mod = sub_mod
let mul = mul
let mul_underspec = mul_underspec
let mul_mod = mul_mod
let div = div
let div_underspec = div_underspec
let rem = rem
let logand = logand
let logor = logor
let logxor = logxor
let lognot = lognot
let shift_right = shift_right
let shift_left = shift_left
assume val eq_mask: a:t -> b:t -> Tot (c:t{(v a = v b <==> v c = pow2 n - 1) /\ (v a <> v b <==> v c = 0)})
assume val gte_mask: a:t -> b:t -> Tot (c:t{(v a >= v b <==> v c = pow2 n - 1) /\ (v a < v b <==> v c = 0)})
let op_Plus_Hat = add
let op_Plus_Question_Hat = add_underspec
let op_Plus_Percent_Hat = add_mod
let op_Subtraction_Hat = sub
let op_Subtraction_Question_Hat = sub_underspec
let op_Subtraction_Percent_Hat = sub_mod
let op_Star_Hat = mul
let op_Star_Question_Hat = mul_underspec
let op_Star_Percent_Hat = mul_mod
let op_Slash_Hat = div
let op_Percent_Hat = rem
let op_Hat_Hat = logxor  
let op_Amp_Hat = logand
let op_Bar_Hat = logor
let op_Less_Less_Hat = shift_left
let op_Greater_Greater_Hat = shift_right
let op_Equal_Hat = eq
let op_Greater_Hat = gt
let op_Greater_Equal_Hat = gte
let op_Less_Hat = gt
let op_Less_Equal_Hat = gte
type byte = t
let of_string = of_string
let uint_to_t = uint_to_t
