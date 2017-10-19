module Spec.Lib.IntTypes

type inttype = 
 | U8 | U16 | U32 | U64 | U128 

let maxint (t:inttype) = 
  match t with
  | U8 -> 0xff
  | U16 -> 0xffff
  | U32 -> 0xffffffff
  | U64 -> 0xffffffffffffffff
  | U128 -> 0xffffffffffffffffffffffffffffffff

unfold 
let bits (n:inttype) = 
  match n with
  | U8 -> 8
  | U16 -> 16
  | U32 -> 32
  | U64 -> 64
  | U128 -> 128

unfold 
let numbytes (n:inttype) = 
  match n with
  | U8 -> 1
  | U16 -> 2
  | U32 -> 4
  | U64 -> 8
  | U128 -> 16
  
val uint_t: t:inttype -> Type0    
val uint_v: #t:inttype -> u:uint_t t -> GTot (n:nat{n <= maxint t})
type uint8 = uint_t U8
type uint16 = uint_t U16
type uint32 = uint_t U32
type uint64 = uint_t U64
type uint128 = uint_t U128

val u8: (n:nat{n <= maxint U8}) -> u:uint8{uint_v #U8 u = n}
val u8uy: (n:FStar.UInt8.t) -> u:uint8{uint_v #U8 u = UInt8.v n}

val u16: (n:nat{n <= maxint U16}) -> u:uint16{uint_v #U16 u = n}
val u32: (n:nat{n <= maxint U32}) -> u:uint32{uint_v #U32 u = n}
val u64: (n:nat{n <= maxint U64}) -> u:uint64{uint_v #U64 u = n}
val u128: (n:nat{n <= maxint U128}) -> u:uint128{uint_v #U128 u = n}

// FOR TRUSTED LIBS ONLY: DONT USE IN CODE OR SPECS >>>>>
val uint_to_nat: #t:inttype -> u:uint_t t -> n:nat{n = uint_v u}
val nat_to_uint: #t:inttype -> (n:nat{n <= maxint t}) -> u:uint_t t{uint_v u = n}
// <<<<< FOR TRUSTED LIBS ONLY: DONT USE IN CODE OR SPECS 

val cast: #t:inttype -> u1:uint_t t -> t':inttype -> u2:uint_t t'{uint_v u2 = uint_v u1 % pow2 (bits t')}

let to_u8 #t u : uint8 = cast #t u U8
let to_u16 #t u : uint16 = cast #t u U16
let to_u32 #t u : uint32 = cast #t u U32
let to_u64 #t u : uint64 = cast #t u U64
let to_u128 #t u : uint128 = cast #t u U128

val add_mod: #t:inttype -> a:uint_t t -> b:uint_t t -> c:uint_t t {uint_v c = (uint_v a + uint_v b) % pow2 (bits t)}

val add: #t:inttype -> a:uint_t t -> b:uint_t t -> Pure (uint_t t)
  (requires (uint_v a + uint_v b < pow2 (bits t)))
  (ensures (fun c -> uint_v c = uint_v a + uint_v b))

val incr: #t:inttype -> a:uint_t t -> Pure (uint_t t)
  (requires (uint_v a < pow2 (bits t) - 1))
  (ensures (fun c -> uint_v c = uint_v a + 1))
  
val mul_mod: #t:inttype{t <> U128} -> a:uint_t t -> b:uint_t t -> c:uint_t t {uint_v c = (uint_v a `op_Multiply` uint_v b) % pow2 (bits t)}

val mul: #t:inttype{t <> U128} -> a:uint_t t -> b:uint_t t -> Pure (uint_t t)
  (requires (uint_v a `op_Multiply` uint_v b < pow2 (bits t)))
  (ensures (fun c -> uint_v c = uint_v a `op_Multiply` uint_v b))

(* I would prefer the post-condition to say: uint_v c = (pow2 (bits t) + uint_v a - uint_v b) % pow2 (bits t) *)
val sub_mod: #t:inttype -> a:uint_t t -> b:uint_t t -> c:uint_t t{uint_v c = (uint_v a - uint_v b) % pow2 (bits t)}
val sub: #t:inttype -> a:uint_t t -> b:uint_t t -> Pure (uint_t t)
  (requires (uint_v a >= uint_v b ))
  (ensures (fun c -> uint_v c = uint_v a - uint_v b))

val decr: #t:inttype -> a:uint_t t -> Pure (uint_t t)
  (requires (uint_v a > 0))
  (ensures (fun c -> uint_v c = uint_v a - 1))

val logxor: #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t 
val logand: #t:inttype -> a:uint_t t  -> 
b:uint_t t -> uint_t t 
val logor: #t:inttype -> a:uint_t t  -> 
b:uint_t t -> uint_t t 
val lognot: #t:inttype -> a:uint_t t -> uint_t t 

val shift_right: #t:inttype -> a:uint_t t -> b:uint32 -> Pure (uint_t t )
  (requires (uint_v #U32 b < bits t))
  (ensures (fun c -> uint_v #t c =  uint_v #t a / pow2 (uint_v #U32 b)))

val shift_left: #t:inttype -> a:uint_t t -> b:uint32 -> Pure (uint_t t )
  (requires (uint_v #U32 b < bits t))
  (ensures (fun c -> uint_v #t c = (uint_v #t a `op_Multiply` pow2 (uint_v #U32 b)) % pow2 (bits t)))

val rotate_right: #t:inttype -> a:uint_t t -> b:uint32 -> Pure (uint_t t )
  (requires (uint_v #U32 b > 0 /\ uint_v #U32 b < bits t))
  (ensures (fun _ -> True))

val rotate_left: #t:inttype -> a:uint_t t -> b:uint32 -> Pure (uint_t t )
  (requires (uint_v #U32 b > 0 /\ uint_v #U32 b < bits t))
  (ensures (fun _ -> True))

val eq_mask: #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

val neq_mask: #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

val gte_mask:  #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

val gt_mask:  #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

val lt_mask:  #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

val lte_mask:  #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

let (+!) = add
let (+.) = add_mod
let ( *! ) = mul
let ( *. ) = mul_mod
let ( -! ) = sub
let ( -. ) = sub_mod
let ( >>. ) = shift_right
let ( <<. ) = shift_left
let ( >>>. ) = rotate_right
let ( <<<. ) = rotate_left
let ( ^. ) = logxor
let ( |. ) = logor
let ( &. ) = logand
let ( ~. ) = lognot

type size_t = n:nat{n <= maxint U32}
val size_to_uint32: s:size_t -> u:uint32{uint_v #U32 u = s}
val size_incr: a:size_t -> Pure (size_t)
  (requires (a < maxint U32))
  (ensures (fun c -> c = a + 1))
val size_decr: a:size_t -> Pure (size_t)
  (requires (a > 0))
  (ensures (fun c -> c = a - 1))


  
val bignum: Type0 
val bn_v: bignum -> GTot nat
val bn: nat -> bignum
val bn_add: bignum -> bignum -> bignum
val bn_mul: bignum -> bignum -> bignum
val bn_sub: a:bignum -> b:bignum{bn_v a >= bn_v b} -> bignum
val bn_mod: bignum -> b:bignum{bn_v b <> 0} -> bignum
val bn_div: bignum -> b:bignum{bn_v b <> 0} -> bignum


