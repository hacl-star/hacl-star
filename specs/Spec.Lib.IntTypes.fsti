module Spec.Lib.IntTypes

type inttype = 
 | U8 | U16 | U32 | U64 | U128 

val maxint: inttype -> nat

unfold 
let bits (n:inttype) = 
  match n with
  | U8 -> 8
  | U16 -> 16
  | U32 -> 32
  | U64 -> 64
  | U128 -> 128

unfold 
let size (n:inttype) = 
  match n with
  | U8 -> 1
  | U16 -> 2
  | U32 -> 4
  | U64 -> 8
  | U128 -> 16
  
val uint: Type0
val ty: uint -> GTot inttype
type uint_t (t:inttype) = 
     u:uint {ty u = t}
val uint_v: u:uint -> GTot nat

type uint8 = uint_t U8
type uint16 = uint_t U16
type uint32 = uint_t U32
type uint64 = uint_t U64
type uint128 = uint_t U128
val u8: (n:nat{n <= maxint U8}) -> u:uint8
val u16: (n:nat{n <= maxint U16}) -> u:uint16
val u32: (n:nat{n <= maxint U32}) -> u:uint32
val u64: (n:nat{n <= maxint U64}) -> u:uint64
val u128: (n:nat{n <= maxint U128}) -> uint128

//val add_mod: a:uint -> b:uint{ty a = ty b} -> u:uint{ty u = ty a}

val add_mod: a:uint -> b:uint -> Pure uint
    (requires (ty b = ty a))
    (ensures (fun u -> ty u = ty a))

val add: a:uint -> b:uint{ty b = ty a /\ 
			 uint_v a + uint_v b < pow2 (bits (ty a))} 
			    -> u:uint{ty u = ty a}
val mul_mod: a:uint -> b:uint{ty b = ty a /\ ty b <> U128} -> u:uint{ty u = ty a}
val mul: a:uint -> b:uint{ty b = ty a /\ ty b <> U128 /\ 
			      uint_v a `op_Multiply` uint_v b < pow2 (bits (ty a))} 
			    -> u:uint{ty u = ty a}
val sub_mod: a:uint -> b:uint{ty b = ty a} -> u:uint{ty u = ty a}
val sub: a:uint -> b:uint{ty b = ty a /\ uint_v a - uint_v b >= 0} -> u:uint{ty u = ty a}

val logxor: a:uint -> b:uint{ty b = ty a} -> u:uint{ty u = ty a}
val logand: a:uint -> b:uint{ty b = ty a} -> u:uint{ty u = ty a}
val logor: a:uint -> b:uint{ty b = ty a} -> u:uint{ty u = ty a}
val lognot: a:uint -> u:uint{ty u = ty a}

val shift_right: a:uint -> b:uint32{uint_v b < bits (ty a)} -> u:uint{ty u = ty a}
val shift_left: a:uint -> b:uint32{uint_v b < bits (ty a)} -> u:uint{ty u = ty a}
val rotate_right: a:uint -> b:uint32{uint_v b > 0 /\ uint_v b < bits (ty a)} -> u:uint{ty u = ty a}
val rotate_left: a:uint -> b:uint32{uint_v b > 0 /\ uint_v b < bits (ty a)} -> u:uint{ty u = ty a}

val eq_mask: a:uint -> b:uint{ty b = ty a} -> c:uint{ty c = ty a }
val neq_mask: a:uint -> b:uint{ty b = ty a} -> c:uint{ty c = ty a}
val gte_mask: a:uint -> b:uint{ty b = ty a} -> c:uint{ty c = ty a}
val gt_mask: a:uint -> b:uint{ty b = ty a} -> c:uint{ty c = ty a}
val lt_mask: a:uint -> b:uint{ty b = ty a} -> c:uint{ty c = ty a}
val lte_mask: a:uint -> b:uint{ty b = ty a} -> c:uint{ty c = ty a}

let op_Plus_Hat = add
let op_Plus_Percent_Hat = add_mod
let op_Multiply_Hat = mul
let op_Multiply_Percent_Hat = mul_mod
let op_Minus_Hat = sub
let op_Minus_Percent_Hat = sub_mod
let op_Greater_Greater_Hat = shift_right
let op_Less_Less_Hat = shift_left
let op_Hat_Hat = logxor
let op_Bar_Hat = logor
let op_Amp_Hat = logand
let op_Greater_Greater_Greater = rotate_right
let op_Less_Less_Less = rotate_left

type index32 = UInt32.t


val bignum: Type0
val bn_v: bignum -> GTot nat
val bn: nat -> bignum
val bn_add: bignum -> bignum -> bignum
val bn_mul: bignum -> bignum -> bignum
val bn_sub: a:bignum -> b:bignum{bn_v a >= bn_v b} -> bignum
val bn_mod: bignum -> b:bignum{bn_v b <> 0} -> bignum
val bn_div: bignum -> b:bignum{bn_v b <> 0} -> bignum

