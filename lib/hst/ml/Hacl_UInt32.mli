type uint32
type t = uint32
           
val n:Prims.int

(* Placeholder, implemented by failwith *)
val v: uint32 -> Prims.int
        
val zero:uint32
val one:uint32
val ones:uint32

val add: uint32 -> uint32 -> uint32
val add_mod: uint32 -> uint32 -> uint32
val sub: uint32 -> uint32 -> uint32
val sub_mod:uint32 -> uint32 -> uint32
val mul:uint32 -> uint32 -> uint32
val mul_mod:uint32 -> uint32 -> uint32
val div:uint32 -> uint32 -> uint32
val rem:uint32 -> uint32 -> uint32

val logand:uint32 -> uint32 -> uint32
val logxor:uint32 -> uint32 -> uint32
val logor:uint32 -> uint32 -> uint32
val lognot:uint32 -> uint32

val shift_left:uint32 -> int -> uint32
val shift_right:uint32 -> int -> uint32

val rotate_left:uint32 -> int -> uint32
val rotate_right:uint32 -> int -> uint32

val op_Hat_Plus: uint32 -> uint32 -> uint32
val op_Hat_Subtraction: uint32 -> uint32 -> uint32
val op_Hat_Star: uint32 -> uint32 -> uint32
val op_Hat_Slash:uint32 -> uint32 -> uint32
val op_Hat_Less_Less:uint32 -> int -> uint32
val op_Hat_Greater_Greater:uint32 -> int -> uint32
val op_Hat_Amp:uint32 -> uint32 -> uint32
val op_Hat_Bar:uint32 -> uint32 -> uint32
val op_Hat_Hat:uint32 -> uint32 -> uint32
val op_Plus_Hat: uint32 -> uint32 -> uint32
val op_Plus_Percent_Hat: uint32 -> uint32 -> uint32
val op_Subtraction_Hat: uint32 -> uint32 -> uint32
val op_Star_Hat: uint32 -> uint32 -> uint32
val op_Slash_Hat:uint32 -> uint32 -> uint32
val op_Less_Less_Hat:uint32 -> int -> uint32
val op_Greater_Greater_Hat:uint32 -> int -> uint32
val op_Amp_Hat:uint32 -> uint32 -> uint32
val op_Bar_Hat:uint32 -> uint32 -> uint32
val op_Hat_Hat:uint32 -> uint32 -> uint32

val of_int: Prims.int -> uint32
val of_string: string -> uint32
                        
val eq_mask:uint32 -> uint32 -> uint32
val gte_mask:uint32 -> uint32 -> uint32

(* Only for realization purposes, does not exists in F* library *)
val to_int: uint32 -> Prims.int
val to_string: uint32 -> string
val to_string_hex: uint32 -> string
val uint_to_t:Prims.int -> uint32
