module Spec.Lib.IntTypes

open FStar.Seq
open FStar.Endianness

(* Declared in .fsti : intsize, bits, maxint *)

let uint_n (t:inttype) : Type0 = 
  match t with
  | U8 -> UInt8.t
  | U16 -> UInt16.t
  | U32 -> UInt32.t
  | U64 -> UInt64.t
  | U128 -> UInt128.t
    
noeq 
type uint_ =
 | UInt: t:inttype -> v:uint_n t -> uint_

let uint = uint_

let ty u = u.t

let uint_v (u:uint) = 
  match u with
  | UInt U8 x -> UInt8.v x
  | UInt U16 x -> UInt16.v x
  | UInt U32 x -> UInt32.v x
  | UInt U64 x -> UInt64.v x
  | UInt U128 x -> UInt128.v x


(* Declared in .fsti: uint8, uint16, uint32, uint64, uint128 *)

let u8 x : uint8 = 
  UInt U8 (UInt8.uint_to_t x)

let u16 x : uint16 = 
  UInt U16 (UInt16.uint_to_t x)

let u32 x : uint32 = 
  UInt U32 (UInt32.uint_to_t x)

let u64 x : uint64 = 
  UInt U64 (UInt64.uint_to_t x)

let u128 x : uint128 = 
  UInt U128 (UInt128.uint_to_t x)

let add_mod #t a b =
  match a,b with
  | UInt U8 a, UInt U8 b -> UInt U8 (UInt8.add_mod a b)
  | UInt U16 a, UInt U16 b -> UInt U16 (UInt16.add_mod a b)
  | UInt U32 a, UInt U32 b -> UInt U32 (UInt32.add_mod a b)
  | UInt U64 a, UInt U64 b -> UInt U64 (UInt64.add_mod a b)
  | UInt U128 a, UInt U128 b -> UInt U128 (UInt128.add_mod a b)
  

let add #t a b = 
  match a,b with
  | UInt U8 a, UInt U8 b -> UInt U8 (UInt8.add a b)
  | UInt U16 a, UInt U16 b -> UInt U16 (UInt16.add a b)
  | UInt U32 a, UInt U32 b -> UInt U32 (UInt32.add a b)
  | UInt U64 a, UInt U64 b -> UInt U64 (UInt64.add a b)
  | UInt U128 a, UInt U128 b -> UInt U128 (UInt128.add a b)


//#reset-options "--z3rlimit 50"

let mul_mod #t a b = 
  match a,b with
  | UInt U8 a, UInt U8 b -> UInt U8 (UInt8.mul_mod a b)
  | UInt U16 a, UInt U16 b -> UInt U16 (UInt16.mul_mod a b)
  | UInt U32 a, UInt U32 b -> UInt U32 (UInt32.mul_mod a b)
  | UInt U64 a, UInt U64 b -> UInt U64 (UInt64.mul_mod a b)


let mul #t a b = 
  match a,b with
  | UInt U8 a, UInt U8 b -> UInt U8 (UInt8.mul a b)
  | UInt U16 a, UInt U16 b -> UInt U16 (UInt16.mul a b)
  | UInt U32 a, UInt U32 b -> UInt U32 (UInt32.mul a b)
  | UInt U64 a, UInt U64 b -> UInt U64 (UInt64.mul a b)


let sub_mod #t a b = 
  match a,b with
  | UInt U8 a, UInt U8 b -> UInt U8 (UInt8.sub_mod a b)
  | UInt U16 a, UInt U16 b -> UInt U16 (UInt16.sub_mod a b)
  | UInt U32 a, UInt U32 b -> UInt U32 (UInt32.sub_mod a b)
  | UInt U64 a, UInt U64 b -> UInt U64 (UInt64.sub_mod a b)
  | UInt U128 a, UInt U128 b -> UInt U128 (UInt128.sub_mod a b)


let sub #t a b = 
  match a,b with
  | UInt U8 a, UInt U8 b -> UInt U8 (UInt8.sub a b)
  | UInt U16 a, UInt U16 b -> UInt U16 (UInt16.sub a b)
  | UInt U32 a, UInt U32 b -> UInt U32 (UInt32.sub a b)
  | UInt U64 a, UInt U64 b -> UInt U64 (UInt64.sub a b)
  | UInt U128 a, UInt U128 b -> UInt U128 (UInt128.sub a b)


let logxor #t a b = 
  match a,b with
  | UInt U8 a, UInt U8 b -> UInt U8 (UInt8.logxor a b)
  | UInt U16 a, UInt U16 b -> UInt U16 (UInt16.logxor a b)
  | UInt U32 a, UInt U32 b -> UInt U32 (UInt32.logxor a b)
  | UInt U64 a, UInt U64 b -> UInt U64 (UInt64.logxor a b)
  | UInt U128 a, UInt U128 b -> UInt U128 (UInt128.logxor a b)


let logand #t a b = 
  match a,b with
  | UInt U8 a, UInt U8 b -> UInt U8 (UInt8.logand a b)
  | UInt U16 a, UInt U16 b -> UInt U16 (UInt16.logand a b)
  | UInt U32 a, UInt U32 b -> UInt U32 (UInt32.logand a b)
  | UInt U64 a, UInt U64 b -> UInt U64 (UInt64.logand a b)
  | UInt U128 a, UInt U128 b -> UInt U128 (UInt128.logand a b)


let logor #t a b = 
  match a,b with
  | UInt U8 a, UInt U8 b -> UInt U8 (UInt8.logor a b)
  | UInt U16 a, UInt U16 b -> UInt U16 (UInt16.logor a b)
  | UInt U32 a, UInt U32 b -> UInt U32 (UInt32.logor a b)
  | UInt U64 a, UInt U64 b -> UInt U64 (UInt64.logor a b)
  | UInt U128 a, UInt U128 b -> UInt U128 (UInt128.logor a b)


let lognot #t a = 
  match a with
  | UInt U8 a -> UInt U8 (UInt8.lognot a)
  | UInt U16 a -> UInt U16 (UInt16.lognot a)
  | UInt U32 a -> UInt U32 (UInt32.lognot a)
  | UInt U64 a -> UInt U64 (UInt64.lognot a)
  | UInt U128 a -> UInt U128 (UInt128.lognot a)


let shift_right #t a b = 
  match a with
  | UInt U8 a -> UInt U8 (UInt8.shift_right a b.v)
  | UInt U16 a -> UInt U16 (UInt16.shift_right a b.v)
  | UInt U32 a -> UInt U32 (UInt32.shift_right a b.v)
  | UInt U64 a -> UInt U64 (UInt64.shift_right a b.v)
  | UInt U128 a -> UInt U128 (UInt128.shift_right a b.v)


let shift_left #t a b = 
  match a with
  | UInt U8 a -> UInt U8 (UInt8.shift_left a b.v)
  | UInt U16 a -> UInt U16 (UInt16.shift_left a b.v)
  | UInt U32 a -> UInt U32 (UInt32.shift_left a b.v)
  | UInt U64 a -> UInt U64 (UInt64.shift_left a b.v)
  | UInt U128 a -> UInt U128 (UInt128.shift_left a b.v)


let rotate_right #t a b = 
  (logor (shift_right a b)  (shift_left a (sub (u32 (bits a.t)) b)))

let rotate_left #t a b = 
  (logor (shift_left a b)  (shift_right a (sub (u32 (bits a.t)) b)))

let eq_mask #t a b = 
  match a,b with
  | UInt U8 a, UInt U8 b -> if FStar.UInt8.(a =^ b) then (u8 (maxint U8)) else (u8 0)
  | UInt U16 a, UInt U16 b -> if FStar.UInt16.(a =^ b) then (u16 (maxint U16)) else (u16 0)
  | UInt U32 a, UInt U32 b -> if FStar.UInt32.(a =^ b) then (u32 (maxint U32)) else (u32 0) 
  | UInt U64 a, UInt U64 b -> if FStar.UInt64.(a =^ b) then (u64 (maxint U64)) else (u64 0) 
  | UInt U128 a, UInt U128 b -> if FStar.UInt128.(a =^ b) then (u128 (maxint U128)) else (u128 0)

let neq_mask #t a b = 
  match a,b with
  | UInt U8 a, UInt U8 b -> if not FStar.UInt8.(a =^ b) then (u8 (maxint U8)) else (u8 0)
  | UInt U16 a, UInt U16 b -> if not FStar.UInt16.(a =^ b) then (u16 (maxint U16)) else (u16 0)
  | UInt U32 a, UInt U32 b -> if not FStar.UInt32.(a =^ b) then (u32 (maxint U32)) else (u32 0) 
  | UInt U64 a, UInt U64 b -> if not FStar.UInt64.(a =^ b) then (u64 (maxint U64)) else (u64 0) 
  | UInt U128 a, UInt U128 b -> if not FStar.UInt128.(a =^ b) then (u128 (maxint U128)) else (u128 0)

let gte_mask #t a b = 
  match a,b with
  | UInt U8 a, UInt U8 b -> if FStar.UInt8.(a >=^ b) then (u8 (maxint U8)) else (u8 0)
  | UInt U16 a, UInt U16 b -> if FStar.UInt16.(a >=^ b) then (u16 (maxint U16)) else (u16 0)
  | UInt U32 a, UInt U32 b -> if FStar.UInt32.(a >=^ b) then (u32 (maxint U32)) else (u32 0) 
  | UInt U64 a, UInt U64 b -> if FStar.UInt64.(a >=^ b) then (u64 (maxint U64)) else (u64 0) 
  | UInt U128 a, UInt U128 b -> if FStar.UInt128.(a >=^ b) then (u128 (maxint U128)) else (u128 0)

let gt_mask #t a b = 
  match a,b with
  | UInt U8 a, UInt U8 b -> if FStar.UInt8.(a >^ b) then (u8 (maxint U8)) else (u8 0)
  | UInt U16 a, UInt U16 b -> if FStar.UInt16.(a >^ b) then (u16 (maxint U16)) else (u16 0)
  | UInt U32 a, UInt U32 b -> if FStar.UInt32.(a >^ b) then (u32 (maxint U32)) else (u32 0) 
  | UInt U64 a, UInt U64 b -> if FStar.UInt64.(a >^ b) then (u64 (maxint U64)) else (u64 0) 
  | UInt U128 a, UInt U128 b -> if FStar.UInt128.(a >^ b) then (u128 (maxint U128)) else (u128 0)


let lt_mask #t a b = 
  match a,b with
  | UInt U8 a, UInt U8 b -> if FStar.UInt8.(a <^ b) then (u8 (maxint U8)) else (u8 0)
  | UInt U16 a, UInt U16 b -> if FStar.UInt16.(a <^ b) then (u16 (maxint U16)) else (u16 0)
  | UInt U32 a, UInt U32 b -> if FStar.UInt32.(a <^ b) then (u32 (maxint U32)) else (u32 0) 
  | UInt U64 a, UInt U64 b -> if FStar.UInt64.(a <^ b) then (u64 (maxint U64)) else (u64 0) 
  | UInt U128 a, UInt U128 b -> if FStar.UInt128.(a <^ b) then (u128 (maxint U128)) else (u128 0)

let lte_mask #t a b = 
  match a,b with
  | UInt U8 a, UInt U8 b -> if FStar.UInt8.(a <=^ b) then (u8 (maxint U8)) else (u8 0)
  | UInt U16 a, UInt U16 b -> if FStar.UInt16.(a <=^ b) then (u16 (maxint U16)) else (u16 0)
  | UInt U32 a, UInt U32 b -> if FStar.UInt32.(a <=^ b) then (u32 (maxint U32)) else (u32 0) 
  | UInt U64 a, UInt U64 b -> if FStar.UInt64.(a <=^ b) then (u64 (maxint U64)) else (u64 0) 
  | UInt U128 a, UInt U128 b -> if FStar.UInt128.(a <=^ b) then (u128 (maxint U128)) else (u128 0)
 
(* defined in .fsti: notations +^, -^, ...*)

type bignum = nat
let bn_v n = n
let bn n = n
let bn_add a b = a + b
let bn_mul a b = a `op_Multiply` b
let bn_sub a b = a - b
let bn_mod a b = a % b
let bn_div a b = a / b


