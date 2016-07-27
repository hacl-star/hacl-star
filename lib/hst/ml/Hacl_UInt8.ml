open Char

let n = Prims.parse_int "8"

type uint8 = int
type t = uint8
type byte = uint8
           
let (zero:uint8) = 0
let (one:uint8) = 1
let (ones:uint8) = 255

let bits = 8

(* Standard operators *)
let add a b = ((a + b) land 255)
let add_mod a b =  (( a +  b) land 255)
let sub a b = (( a -  b) land 255)
let sub_mod a b =  (( a -  b) land 255)
let mul a b =  (( a *  b) land 255)
let mul_mod a b =  (( a *  b) land 255)
let div a b =  (( a /  b) land 255)
let rem a b =  ( a mod  b)

let logand a b =  ( a land  b)
let logxor a b =  ( a lxor  b)
let logor a b =  ( a lor  b)
let lognot a =  (lnot ( a land 255))

let shift_left a s = (a lsl s) land 255
let shift_right a s = (a lsr s) land 255

let rotate_left a s =  ((( a lsl s) + ( a lsr (8-s))) land 255)
let rotate_right a s =  ((( a lsl (8-s)) + ( a lsr s)) land 255)

let gte_mask x y = (lnot((x - y) asr 7)) land 255
let eq_mask x y = gte_mask x y land gte_mask y x
let lt_mask x y = lnot (gte_mask x y)
                                           
let op_Hat_Plus = add
let op_Hat_Subtraction = sub
let op_Hat_Star = mul
let op_Hat_Slash = div
let op_Hat_Plus_Percent = add_mod
let op_Hat_Star_Percent = mul_mod
let op_Hat_Subtraction_Percent = sub_mod
let op_Hat_Less_Less  = shift_left
let op_Hat_Greater_Greater  = shift_right
let op_Hat_Amp = logand
let op_Hat_Hat = logxor
let op_Hat_Bar = logor

let op_Plus_Hat = add
let op_Subtraction_Hat = sub
let op_Star_Hat = mul
let op_Slash_Hat = div
let op_Plus_Hat_Percent = add_mod
let op_Star_Hat_Percent = mul_mod
let op_Subtraction_Hat_Percent = sub_mod
let op_Less_Less_Hat = shift_left
let op_Greater_Greater_Hat = shift_right
let op_Amp_Hat = logand
let op_Hat_Hat = logxor
let op_Bar_Hat = logor

let of_string s =
  let x = int_of_string s in
  if x >= 256 || x < 0 then failwith "Wrong constant"
  else x 
let of_int s = Z.to_int (Z.logand s (Z.of_int 255))
                                                             
let to_string s = string_of_int s
let to_string_hex s = Printf.sprintf "%02x" s
let to_int s = Z.of_int s
let uint_to_t s = Z.to_int s
