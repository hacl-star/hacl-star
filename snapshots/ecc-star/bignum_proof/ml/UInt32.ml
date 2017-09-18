
open Prims
open Stdint
       
let bitsize = (fun x n -> true)

type ' n ulint =
Prims.int

type uintN =
Prims.unit ulint

let fits_size = (fun n x m -> ())

let fits_platform_size = (fun n x -> ())

let size_of_add_lemma = (fun n a m b -> ())

let size_of_sub_lemma = (fun n a m b -> ())

let size_of_mul_lemma = (fun n a m b -> ())

let size_of_mul_by_pow2 = (fun n a m -> ())

let add = (fun size a b -> (let _18_70 = ()
in (a + b)))

let sub = (fun size a b -> (let _18_80 = ()
in (a - b)))

let mul = (fun size a b -> (let _18_90 = ()
in (let _18_92 = ()
in (a * b))))

let mul' = (fun size a b -> (let _18_102 = ()
in (let _18_104 = ()
in (a * b))))

let div = (fun size a b -> (let _18_114 = ()
in (let _18_116 = ()
in (a / b))))

type uint_wide = Uint64
type uint_std = Uint32

let byte_to_limb = Uint32.of_uint8
let byte_to_wide = Uint64.of_uint8		     		  
let limb_to_wide = Uint32.to_uint64
let wide_to_limb = Uint32.of_uint64
let to_limb = Uint32.of_string
let to_wide = Uint64.of_string

let byte_to_int = Uint8.to_int
let limb_to_int = Uint32.to_int
let wide_to_int = Uint64.to_int		    

let zero_byte = Uint8.zero		
let zero_limb = Uint32.zero
let zero_wide = Uint64.zero		  
let one_byte = Uint8.one
let one_limb = Uint32.one
let one_wide = Uint64.one		  
		     		     
let add_byte = Uint8.add
let mul_byte = Uint8.mul		
let sub_byte = Uint8.sub
let div_byte = Uint8.div
let mod_byte = Uint8.rem
let neg_byte = Uint8.neg
let log_and_byte = Uint8.logand
let log_or_byte = Uint8.logor
let log_xor_byte = Uint8.logxor
let log_not_byte = Uint8.lognot
let to_uint_byte x = Uint8.of_string (string_of_int x)
let shift_left_byte = Uint8.shift_left
let shift_right_byte = Uint8.shift_right

let add_std = Uint32.add
let mul_std = Uint32.mul		
let mul_std_to_wide x y = Uint64.mul (Uint32.to_uint64 x) (Uint32.to_uint64 y)
let sub_std = Uint32.sub
let div_std = Uint32.div
let mod_std = Uint32.rem
let neg_std = Uint32.neg
let log_and_std = Uint32.logand
let log_or_std = Uint32.logor
let log_xor_std = Uint32.logxor
let log_not_std = Uint32.lognot
let to_uint_std x = Uint32.of_string (string_of_int x)
let shift_left_std = Uint32.shift_left
let shift_right_std = Uint32.shift_right

let add_wide = Uint64.add
let mul_wide = Uint64.mul
let sub_wide = Uint64.sub
let div_wide = Uint64.div
let mod_wide = Uint64.rem
let neg_wide = Uint64.neg
let log_and_wide = Uint64.logand
let log_or_wide = Uint64.logor
let log_xor_wide = Uint64.logxor
let log_not_wide = Uint64.lognot
let to_uint_wide x = Uint64.of_string (string_of_int x)
let shift_left_wide = Uint64.shift_left
let shift_right_wide = Uint64.shift_right
			 
let eq_limb x y =
  let a = Uint32.lognot (Uint32.logxor x y) in
  let a = Uint32.logand a (Uint32.shift_left a 16) in
  let a = Uint32.logand a (Uint32.shift_left a 8) in
  let a = Uint32.logand a (Uint32.shift_left a 4) in
  let a = Uint32.logand a (Uint32.shift_left a 2) in
  let a = Uint32.logand a (Uint32.shift_left a 1) in
  (*  let b = Stdint.Int32.of_string (Uint32.to_string_hex a) in *)
  let b = Stdint.Int32.of_uint32 a in
  let b = Stdint.Int32.shift_right b 31 in
  (* Uint32.of_string (Stdint.Int32.to_string_hex b) *)
  Uint32.of_int32 b

let eq_wide x y =
  let a = Uint64.lognot (Uint64.logxor x y) in
  let a = Uint64.logand a (Uint64.shift_left a 32) in
  let a = Uint64.logand a (Uint64.shift_left a 16) in
  let a = Uint64.logand a (Uint64.shift_left a 8) in
  let a = Uint64.logand a (Uint64.shift_left a 4) in
  let a = Uint64.logand a (Uint64.shift_left a 2) in
  let a = Uint64.logand a (Uint64.shift_left a 1) in
  let b = Stdint.Int64.of_string (Uint64.to_string_hex a) in
  let b = Stdint.Int64.shift_right b 63 in
  Uint64.of_string (Stdint.Int64.to_string_hex b)

let gte_limb x y =
  let a = Uint32.sub x y in
  (* let b = Stdint.Int32.of_string (Uint32.to_string_hex a) in *)
  let b = Stdint.Int32.of_uint32 a in
  let b = Stdint.Int32.shift_right b 31 in
  (* let c = Uint32.of_string (Stdint.Int32.to_string_hex b) in *)
  let c = Uint32.of_int32 b in
  Uint32.lognot c	

let gte_wide x y =
  let a = Uint64.sub x y in
  let b = Stdint.Int64.of_string (Uint64.to_string_hex a) in
  let b = Stdint.Int64.shift_right b 63 in
  let c = Uint64.of_string (Stdint.Int64.to_string_hex b) in
  Uint64.lognot c


type ' max utint = Uint32.t
		     
let sizeOf = 0
let valueOf = (fun max n -> n)
let of_int = (fun max_size size v -> Uint32.of_int v)

let lemma_1 = (fun max_size size v -> ())

let lemma_2 = (fun max_size size v -> ())

type uint = Uint32.t

let zero' = (fun max_size -> Uint32.zero)

let one' = (fun max_size -> Uint32.one)




