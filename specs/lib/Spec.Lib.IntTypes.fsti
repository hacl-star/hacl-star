module Spec.Lib.IntTypes

type inttype = 
 | U8 | U16 | U32 | U64 | U128 

inline_for_extraction
unfold
let maxint (t:inttype) = 
  match t with
  | U8 -> 0xff
  | U16 -> 0xffff
  | U32 -> 0xffffffff
  | U64 -> 0xffffffffffffffff
  | U128 -> 0xffffffffffffffffffffffffffffffff

inline_for_extraction
unfold 
let bits (n:inttype) = 
  match n with
  | U8 -> 8
  | U16 -> 16
  | U32 -> 32
  | U64 -> 64
  | U128 -> 128

inline_for_extraction
unfold 
let numbytes (n:inttype) = 
  match n with
  | U8 -> 1
  | U16 -> 2
  | U32 -> 4
  | U64 -> 8
  | U128 -> 16
  
inline_for_extraction
val uint_t: t:inttype -> Type0    
inline_for_extraction
val uint_v: #t:inttype -> u:uint_t t -> GTot (n:nat{n <= maxint t})

inline_for_extraction
type uint8 = uint_t U8
inline_for_extraction
type uint16 = uint_t U16
inline_for_extraction
type uint32 = uint_t U32
inline_for_extraction
type uint64 = uint_t U64
inline_for_extraction
type uint128 = uint_t U128

inline_for_extraction
val u8: (n:nat{n <= maxint U8}) -> u:uint8{uint_v #U8 u = n}
inline_for_extraction
val u8uy: (n:FStar.UInt8.t) -> u:uint8{uint_v #U8 u = UInt8.v n}

inline_for_extraction
val u16: (n:nat{n <= maxint U16}) -> u:uint16{uint_v #U16 u = n}
inline_for_extraction
val u32: (n:nat{n <= maxint U32}) -> u:uint32{uint_v #U32 u = n}
inline_for_extraction
val u64: (n:nat{n <= maxint U64}) -> u:uint64{uint_v #U64 u = n}
inline_for_extraction
val u128: (n:nat{n <= maxint U128}) -> u:uint128{uint_v #U128 u = n}

inline_for_extraction
val nat_to_uint: #t:inttype -> (n:nat{n <= maxint t}) -> u:uint_t t{uint_v u = n}
// FOR TRUSTED LIBS ONLY: DONT USE IN CODE OR SPECS >>>>>
inline_for_extraction
val uint_to_nat: #t:inttype -> u:uint_t t -> n:nat{n = uint_v u}
// <<<<< FOR TRUSTED LIBS ONLY: DONT USE IN CODE OR SPECS 

inline_for_extraction
val cast: #t:inttype -> t':inttype -> u1:uint_t t -> u2:uint_t t'{uint_v u2 = uint_v u1 % pow2 (bits t')}

inline_for_extraction
let to_u8 #t u : uint8 = cast #t U8 u
inline_for_extraction
let to_u16 #t u : uint16 = cast #t U16 u
inline_for_extraction
let to_u32 #t u : uint32 = cast #t U32 u
inline_for_extraction
let to_u64 #t u : uint64 = cast #t U64 u
inline_for_extraction
let to_u128 #t u : uint128 = cast #t U128 u

inline_for_extraction
val add_mod: #t:inttype -> a:uint_t t -> b:uint_t t -> c:uint_t t {uint_v c = (uint_v a + uint_v b) % pow2 (bits t)}


inline_for_extraction
val add: #t:inttype -> a:uint_t t -> b:uint_t t -> Pure (uint_t t)
  (requires (uint_v a + uint_v b < pow2 (bits t)))
  (ensures (fun c -> uint_v c = uint_v a + uint_v b))

inline_for_extraction
val incr: #t:inttype -> a:uint_t t -> Pure (uint_t t)
  (requires (uint_v a < pow2 (bits t) - 1))
  (ensures (fun c -> uint_v c = uint_v a + 1))
  
inline_for_extraction
val mul_mod: #t:inttype{t <> U128} -> a:uint_t t -> b:uint_t t -> c:uint_t t {uint_v c = (uint_v a `op_Multiply` uint_v b) % pow2 (bits t)}

inline_for_extraction
val mul: #t:inttype{t <> U128} -> a:uint_t t -> b:uint_t t -> Pure (uint_t t)
  (requires (uint_v a `op_Multiply` uint_v b < pow2 (bits t)))
  (ensures (fun c -> uint_v c = uint_v a `op_Multiply` uint_v b))

(* I would prefer the post-condition to say: uint_v c = (pow2 (bits t) + uint_v a - uint_v b) % pow2 (bits t) *)
inline_for_extraction
val sub_mod: #t:inttype -> a:uint_t t -> b:uint_t t -> c:uint_t t{uint_v c = (uint_v a - uint_v b) % pow2 (bits t)}
inline_for_extraction
val sub: #t:inttype -> a:uint_t t -> b:uint_t t -> Pure (uint_t t)
  (requires (uint_v a >= uint_v b ))
  (ensures (fun c -> uint_v c = uint_v a - uint_v b))

inline_for_extraction
val decr: #t:inttype -> a:uint_t t -> Pure (uint_t t)
  (requires (uint_v a > 0))
  (ensures (fun c -> uint_v c = uint_v a - 1))

inline_for_extraction
val logxor: #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t 
inline_for_extraction
val logand: #t:inttype -> a:uint_t t  -> 
b:uint_t t -> uint_t t 
inline_for_extraction
val logor: #t:inttype -> a:uint_t t  -> 
b:uint_t t -> uint_t t 
inline_for_extraction
val lognot: #t:inttype -> a:uint_t t -> uint_t t 

inline_for_extraction
val shift_right: #t:inttype -> a:uint_t t -> b:uint32 -> Pure (uint_t t )
  (requires (uint_v #U32 b < bits t))
  (ensures (fun c -> uint_v #t c =  uint_v #t a / pow2 (uint_v #U32 b)))

inline_for_extraction
val shift_left: #t:inttype -> a:uint_t t -> b:uint32 -> Pure (uint_t t )
  (requires (uint_v #U32 b < bits t))
  (ensures (fun c -> uint_v #t c = (uint_v #t a `op_Multiply` pow2 (uint_v #U32 b)) % pow2 (bits t)))

inline_for_extraction
val rotate_right: #t:inttype -> a:uint_t t -> b:uint32 -> Pure (uint_t t )
  (requires (uint_v #U32 b > 0 /\ uint_v #U32 b < bits t))
  (ensures (fun _ -> True))

inline_for_extraction
val rotate_left: #t:inttype -> a:uint_t t -> b:uint32 -> Pure (uint_t t )
  (requires (uint_v #U32 b > 0 /\ uint_v #U32 b < bits t))
  (ensures (fun _ -> True))

inline_for_extraction
val eq_mask: #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

inline_for_extraction
val neq_mask: #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

inline_for_extraction
val gte_mask:  #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

inline_for_extraction
val gt_mask:  #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

inline_for_extraction
val lt_mask:  #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

inline_for_extraction
val lte_mask:  #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

inline_for_extraction
let (+!) = add
inline_for_extraction
let (+.) = add_mod
inline_for_extraction
let ( *! ) = mul
inline_for_extraction
let ( *. ) = mul_mod
inline_for_extraction
let ( -! ) = sub
inline_for_extraction
let ( -. ) = sub_mod
inline_for_extraction
let ( >>. ) = shift_right
inline_for_extraction
let ( <<. ) = shift_left
inline_for_extraction
let ( >>>. ) = rotate_right
inline_for_extraction
let ( <<<. ) = rotate_left
inline_for_extraction
let ( ^. ) = logxor
inline_for_extraction
let ( |. ) = logor
inline_for_extraction
let ( &. ) = logand
inline_for_extraction
let ( ~. ) = lognot

inline_for_extraction
type size_t = n:nat{n <= maxint U32}

inline_for_extraction
val size_to_uint32: s:size_t -> u:uint32{uint_v #U32 u = s}
inline_for_extraction
val size_incr: a:size_t -> Pure (size_t)
  (requires (a < maxint U32))
  (ensures (fun c -> c = a + 1))
inline_for_extraction
val size_decr: a:size_t -> Pure (size_t)
  (requires (a > 0))
  (ensures (fun c -> c = a - 1))


  
inline_for_extraction
val bignum: Type0 
inline_for_extraction
val bn_v: bignum -> GTot nat
inline_for_extraction
val bn: nat -> bignum
inline_for_extraction
val bn_add: bignum -> bignum -> bignum
inline_for_extraction
val bn_mul: bignum -> bignum -> bignum
inline_for_extraction
val bn_sub: a:bignum -> b:bignum{bn_v a >= bn_v b} -> bignum
inline_for_extraction
val bn_mod: bignum -> b:bignum{bn_v b <> 0} -> bignum
inline_for_extraction
val bn_div: bignum -> b:bignum{bn_v b <> 0} -> bignum


