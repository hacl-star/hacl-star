type uint128
type t = uint128

type u32 = FStar_UInt32.t
             
val n:Prims.int

val v: uint128 -> Prims.int
        
val add: uint128 -> uint128 -> uint128
val add_mod: uint128 -> uint128 -> uint128
val sub: uint128 -> uint128 -> uint128
val sub_mod:uint128 -> uint128 -> uint128
val mul:uint128 -> uint128 -> uint128
val mul_mod:uint128 -> uint128 -> uint128
val mul_wide: Hacl_UInt64.t -> Hacl_UInt64.t -> uint128
val div:uint128 -> uint128 -> uint128
val rem:uint128 -> uint128 -> uint128

val logand:uint128 -> uint128 -> uint128
val logxor:uint128 -> uint128 -> uint128
val logor:uint128 -> uint128 -> uint128
val lognot:uint128 -> uint128

val shift_left:uint128 -> u32 -> uint128
val shift_right:uint128 -> u32 -> uint128
                  
val op_Plus_Hat: uint128 -> uint128 -> uint128
val op_Plus_Percent_Hat: uint128 -> uint128 -> uint128
val op_Subtraction_Hat: uint128 -> uint128 -> uint128
val op_Subtraction_Percent_Hat: uint128 -> uint128 -> uint128
val op_Star_Hat: Hacl_UInt64.t -> Hacl_UInt64.t -> uint128
(* val op_Star_Percent_Hat: uint128 -> uint128 -> uint128 *)
val op_Less_Less_Hat:uint128 -> u32 -> uint128
val op_Greater_Greater_Hat:uint128 -> u32 -> uint128
val op_Amp_Hat:uint128 -> uint128 -> uint128
val op_Bar_Hat:uint128 -> uint128 -> uint128
val op_Hat_Hat:uint128 -> uint128 -> uint128

val of_string: string -> uint128
val of_int: Prims.int -> uint128
                        
val eq_mask:uint128 -> uint128 -> uint128
val gte_mask:uint128 -> uint128 -> uint128
val lt_mask:uint128 -> uint128 -> uint128

(* Only for realization purposes, does not exists in F* library *)
val to_string: uint128 -> string
val uint_to_t:Prims.int -> uint128
