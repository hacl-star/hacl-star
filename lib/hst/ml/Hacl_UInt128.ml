type uint128 = Stdint.Uint128.t
type u32 = int
type t = uint128

let n = Prims.parse_int "128"

let (%) x y = if x < 0 then (x mod y) + y else x mod y

let v (x:uint128) : Prims.int = failwith "Ghost function, cannot be called in concrete code"

let zero = Stdint.Uint128.zero
let one = Stdint.Uint128.one
let ones = Stdint.Uint128.pred Stdint.Uint128.zero

let add (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.add a b
let add_underspec a b = add a b
let add_mod a b = add a b

let sub (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.sub a b
let sub_underspec a b = sub a b
let sub_mod a b = sub a b

let mul (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.mul a b
let mul_underspec a b = mul a b
let mul_mod a b = mul a b
let mul_wide (a:Hacl_UInt64.t) (b:Hacl_UInt64.t) = Stdint.Uint128.mul (Stdint.Uint128.of_string (Hacl_UInt64.to_string a))
                                                                          (Stdint.Uint128.of_string (Hacl_UInt64.to_string b))
                                                          
let div (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.div a b

let rem (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.rem a b

let logand (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.logand a b
let logxor (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.logxor a b
let logor  (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.logor a b
let lognot (a:uint128) : uint128 = Stdint.Uint128.lognot a

(* let cmod (x:Prims.int) : Prims.int = *)
(*   if Prims.op_GreaterThan x (Prims.parse_int "9223372036854775807") *)
(*   then Prims.op_Subtraction x (Prims.parse_int "18446744073709551616") *)
(*   else x *)
                                              
let int_to_uint128 (x:Prims.int) : uint128 = Stdint.Uint128.of_string (Prims.to_string x) 

let shift_right (a:uint128) (b:u32) : uint128 = Stdint.Uint128.shift_right_logical a b
let shift_left  (a:uint128) (b:u32) : uint128 = Stdint.Uint128.shift_left a b

(* Comparison operators *)
(* TODO *)
let eq_mask x y = if x = y then Stdint.Uint128.pred Stdint.Uint128.zero else Stdint.Uint128.zero
(* TODO *)
let gte_mask x y = if x >= y then Stdint.Uint128.pred Stdint.Uint128.zero else Stdint.Uint128.zero
let lt_mask x y = lognot (gte_mask x y)

(* Infix notations *)
let op_Plus_Hat = add
let op_Plus_Question_Hat = add_underspec
let op_Plus_Hat_Percent = add_mod
let op_Subtraction_Hat = sub
let op_Subtraction_Question_Hat = sub_underspec
let op_Subtraction_Hat_Percent = sub_mod
let op_Star_Hat = mul
let op_Star_Question_Hat = mul_underspec
let op_Star_Hat_Percent = mul_mod
let op_Slash_Hat = div
let op_Percent_Hat = rem
let op_Hat_Hat = logxor  
let op_Amp_Hat = logand
let op_Bar_Hat = logor
let op_Less_Less_Hat = shift_left
let op_Greater_Greater_Hat = shift_right

let op_Hat_Plus = add
let op_Hat_Plus_Question = add_underspec
let op_Hat_Plus_Percent = add_mod
let op_Hat_Subtraction = sub
let op_Hat_Subtraction_Question = sub_underspec
let op_Hat_Subtraction_Percent = sub_mod
let op_Hat_Star = mul
let op_Hat_Star_Question = mul_underspec
let op_Hat_Star_Percent = mul_mod
let op_Hat_Slash = div
let op_Hat_Percent = rem
let op_Hat_Hat = logxor  
let op_Hat_Amp = logand
let op_Hat_Bar = logor
let op_Hat_Less_Less = shift_left
let op_Hat_Greater_Greater = shift_right                               
                          
let of_string s = Stdint.Uint128.of_string s
let to_string s = Stdint.Uint128.to_string s
let uint_to_t s = Stdint.Uint128.of_string (Z.to_string s)
let of_int = uint_to_t
let to_int s = Prims.parse_int (Stdint.Uint128.to_string s)
