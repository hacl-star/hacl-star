type uint8
type t = uint8
type byte = uint8
       
val n:Prims.int
       
val zero:uint8
val one:uint8
val ones:uint8

val add: uint8 -> uint8 -> uint8
val add_mod: uint8 -> uint8 -> uint8
val sub: uint8 -> uint8 -> uint8
val sub_mod:uint8 -> uint8 -> uint8
val mul:uint8 -> uint8 -> uint8
val mul_mod:uint8 -> uint8 -> uint8
val div:uint8 -> uint8 -> uint8
val rem:uint8 -> uint8 -> uint8

val logand:uint8 -> uint8 -> uint8
val logxor:uint8 -> uint8 -> uint8
val logor:uint8 -> uint8 -> uint8
val lognot:uint8 -> uint8

val shift_left:uint8 -> int -> uint8
val shift_right:uint8 -> int -> uint8

val rotate_left:uint8 -> int -> uint8
val rotate_right:uint8 -> int -> uint8

val op_Hat_Plus: uint8 -> uint8 -> uint8
val op_Hat_Subtraction: uint8 -> uint8 -> uint8
val op_Hat_Star: uint8 -> uint8 -> uint8
val op_Hat_Plus_Percent: uint8 -> uint8 -> uint8
val op_Hat_Subtraction_Percent: uint8 -> uint8 -> uint8
val op_Hat_Star_Percent: uint8 -> uint8 -> uint8
val op_Hat_Slash:uint8 -> uint8 -> uint8
val op_Hat_Less_Less:uint8 -> int -> uint8
val op_Hat_Greater_Greater:uint8 -> int -> uint8
val op_Hat_Amp:uint8 -> uint8 -> uint8
val op_Hat_Bar:uint8 -> uint8 -> uint8
val op_Hat_Hat:uint8 -> uint8 -> uint8

val op_Plus_Hat: uint8 -> uint8 -> uint8
val op_Subtraction_Hat: uint8 -> uint8 -> uint8
val op_Star_Hat: uint8 -> uint8 -> uint8
val op_Plus_Hat_Percent: uint8 -> uint8 -> uint8
val op_Subtraction_Hat_Percent: uint8 -> uint8 -> uint8
val op_Star_Hat_Percent: uint8 -> uint8 -> uint8
val op_Slash_Hat:uint8 -> uint8 -> uint8
val op_Less_Less_Hat:uint8 -> int -> uint8
val op_Greater_Greater_Hat:uint8 -> int -> uint8
val op_Amp_Hat:uint8 -> uint8 -> uint8
val op_Bar_Hat:uint8 -> uint8 -> uint8
val op_Hat_Hat:uint8 -> uint8 -> uint8

val of_int: Prims.int -> uint8
val of_string: string -> uint8
                                
val eq_mask:uint8 -> uint8 -> uint8
val gte_mask:uint8 -> uint8 -> uint8
val lt_mask:uint8 -> uint8 -> uint8

(* Only for realization purposes, not in F* library *)
val uint_to_t:Prims.int -> uint8
val to_int:uint8 -> Prims.int
val to_string: uint8 -> string
val to_string_hex: uint8 -> string
