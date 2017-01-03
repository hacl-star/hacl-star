type uint16
type t = uint16
           
val n:Prims.int

(* Placeholder, implemented by failwith *)
val v: uint16 -> Prims.int
        
val zero:uint16
val one:uint16
val ones:uint16

val add: uint16 -> uint16 -> uint16
val add_mod: uint16 -> uint16 -> uint16
val sub: uint16 -> uint16 -> uint16
val sub_mod:uint16 -> uint16 -> uint16
val mul:uint16 -> uint16 -> uint16
val mul_mod:uint16 -> uint16 -> uint16
val div:uint16 -> uint16 -> uint16
val rem:uint16 -> uint16 -> uint16

val logand:uint16 -> uint16 -> uint16
val logxor:uint16 -> uint16 -> uint16
val logor:uint16 -> uint16 -> uint16
val lognot:uint16 -> uint16

val shift_left:uint16 -> int -> uint16
val shift_right:uint16 -> int -> uint16

val rotate_left:uint16 -> int -> uint16
val rotate_right:uint16 -> int -> uint16

val op_Hat_Plus: uint16 -> uint16 -> uint16
val op_Hat_Subtraction: uint16 -> uint16 -> uint16
val op_Hat_Star: uint16 -> uint16 -> uint16
val op_Hat_Slash:uint16 -> uint16 -> uint16
val op_Hat_Less_Less:uint16 -> int -> uint16
val op_Hat_Greater_Greater:uint16 -> int -> uint16
val op_Hat_Amp:uint16 -> uint16 -> uint16
val op_Hat_Bar:uint16 -> uint16 -> uint16
val op_Hat_Hat:uint16 -> uint16 -> uint16
val op_Plus_Hat: uint16 -> uint16 -> uint16
val op_Plus_Percent_Hat: uint16 -> uint16 -> uint16
val op_Subtraction_Hat: uint16 -> uint16 -> uint16
val op_Star_Hat: uint16 -> uint16 -> uint16
val op_Slash_Hat:uint16 -> uint16 -> uint16
val op_Less_Less_Hat:uint16 -> int -> uint16
val op_Greater_Greater_Hat:uint16 -> int -> uint16
val op_Amp_Hat:uint16 -> uint16 -> uint16
val op_Bar_Hat:uint16 -> uint16 -> uint16
val op_Hat_Hat:uint16 -> uint16 -> uint16

val of_int: Prims.int -> uint16
val of_string: string -> uint16
                        
val eq_mask:uint16 -> uint16 -> uint16
val gte_mask:uint16 -> uint16 -> uint16
val lt_mask:uint16 -> uint16 -> uint16

(* Only for realization purposes, does not exists in F* library *)
val to_int: uint16 -> Prims.int
val to_string: uint16 -> string
val to_string_hex: uint16 -> string
val uint_to_t:Prims.int -> uint16
