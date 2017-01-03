
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

type uint_wide = uint128
type uint_std = uint64
type limb = uint_std
type wide = uint_wide              
                  
let byte_to_limb:uint8 -> limb = Uint64.of_uint8
let byte_to_wide = Uint128.of_uint8
let limb_to_byte = Uint64.to_uint8
let limb_to_wide = Uint64.to_uint128
let wide_to_byte = Uint128.to_uint8                     
let wide_to_limb = Uint64.of_uint128
let to_limb = Uint64.of_string
let to_wide = Uint128.of_string

let byte_to_int = Uint8.to_int
let limb_to_int = Uint64.to_int
let wide_to_int = Uint128.to_int		    
		
let zero_byte = Uint8.zero
let zero_limb = Uint64.zero
let zero_wide = Uint128.zero
let one_byte = Uint8.one
let one_limb = Uint64.one
let one_wide = Uint128.one		  
		     
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

let add_limb = Uint64.add
let mul_limb = Uint64.mul		
let mul_limb_to_wide x y = Uint128.mul (Uint64.to_uint128 x) (Uint64.to_uint128 y)
let sub_limb = Uint64.sub
let sub_mod_limb = Uint64.sub
let div_limb = Uint64.div
let mod_limb = Uint64.rem
let neg_limb = Uint64.neg
let log_and_limb = Uint64.logand
let log_or_limb = Uint64.logor
let log_xor_limb = Uint64.logxor
let log_not_limb = Uint64.lognot
let to_uint_limb x = Uint64.of_string (string_of_int x)
let shift_left_limb = Uint64.shift_left
let shift_right_limb = Uint64.shift_right

let add_wide = Uint128.add
let mul_wide = Uint128.mul
let sub_wide = Uint128.sub
let sub_mod_wide = Uint128.sub
let div_wide = Uint128.div
let mod_wide = Uint128.rem
let neg_wide = Uint128.neg
let log_and_wide = Uint128.logand
let log_or_wide = Uint128.logor
let log_xor_wide = Uint128.logxor
let log_not_wide = Uint128.lognot
let to_uint_wide x = Uint128.of_string (string_of_int x)
let shift_left_wide = Uint128.shift_left
let shift_right_wide = Uint128.shift_right

let eq_limb x y =
  let a = Uint64.lognot (Uint64.logxor x y) in
  let a = Uint64.logand a (Uint64.shift_left a 32) in
  let a = Uint64.logand a (Uint64.shift_left a 16) in
  let a = Uint64.logand a (Uint64.shift_left a 8) in
  let a = Uint64.logand a (Uint64.shift_left a 4) in
  let a = Uint64.logand a (Uint64.shift_left a 2) in
  let a = Uint64.logand a (Uint64.shift_left a 1) in
  let b = Stdint.Int64.of_uint64 a in
  (*  let b = Stdint.Int64.of_string (Uint64.to_string_hex a) in *)
  let b = Stdint.Int64.shift_right b 63 in
  (*  Uint64.of_string (Stdint.Int64.to_string_hex b) *)
  Uint64.of_int64 b	       

let eq_wide x y =
  let a = Uint128.lognot (Uint128.logxor x y) in
  let a = Uint128.logand a (Uint128.shift_left a 64) in
  let a = Uint128.logand a (Uint128.shift_left a 32) in
  let a = Uint128.logand a (Uint128.shift_left a 16) in
  let a = Uint128.logand a (Uint128.shift_left a 8) in
  let a = Uint128.logand a (Uint128.shift_left a 4) in
  let a = Uint128.logand a (Uint128.shift_left a 2) in
  let a = Uint128.logand a (Uint128.shift_left a 1) in
  let b = Int128.of_uint128 a in
  (* let b = Stdint.Int128.of_string (Uint128.to_string_hex a) in *)
  let b = Stdint.Int128.shift_right b 127 in
  Uint128.of_int128 b
  (* Uint128.of_string (Stdint.Int128.to_string_hex b) *)

(* Requires x < 2^63 and y < 2 ^ 63 *)
let gte_limb x y =
  let a = Uint64.sub x y in
  (*  let b = Stdint.Int64.of_string (Uint64.to_string_hex a) in *)
  let b = Stdint.Int64.of_uint64 a in
  let b = Stdint.Int64.shift_right b 63 in
  (* let c = Uint64.of_string (Stdint.Int64.to_string_hex b) in *)
  let c = Uint64.of_int64 b in
  Uint64.lognot c	

(* Requires x < 2^127 and y < 2 ^ 127 *)
let gte_wide x y =
  let a = Uint128.sub x y in
  (* let b = Stdint.Int128.of_string (Uint128.to_string_hex a) in *)
  let b = Int128.of_uint128 a in
  let b = Int128.shift_right b 127 in
  (* let c = Uint128.of_string (Stdint.Int128.to_string_hex b) in *)
  let c = Uint128.of_int128 b in
  Uint128.lognot c
 
type ' max utint = Uint64.t
		     
let sizeOf = 0
let valueOf = (fun max n -> n)
let of_int = (fun max_size size v -> Uint64.of_int v)

let lemma_1 = (fun max_size size v -> ())

let lemma_2 = (fun max_size size v -> ())

type uint = Uint64.t

let zero' = (fun max_size -> Uint64.zero)

let one' = (fun max_size -> Uint64.one)

let to_string s = Uint64.to_string s
let of_string s = Uint64.of_string s
let wide_to_string s = Uint128.to_string s
let wide_of_string s = Uint128.of_string s
let of_int64 s = Uint64.of_int64 s
let to_int64 s = Uint64.to_int64 s
