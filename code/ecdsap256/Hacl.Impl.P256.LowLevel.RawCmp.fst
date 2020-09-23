module Hacl.Impl.P256.LowLevel.RawCmp


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Lib.RawIntTypes

inline_for_extraction noextract
val eq_u8_nCT: a:uint8 -> b:uint8 -> (r:bool{r == (uint_v a = uint_v b)})

let eq_u8_nCT a b =
  let open Lib.RawIntTypes in
  FStar.UInt8.(u8_to_UInt8 a =^ u8_to_UInt8 b)


inline_for_extraction noextract
val eq_u64_nCT: a:uint64 -> b:uint64 -> (r:bool{r == (uint_v a = uint_v b)})

let eq_u64_nCT a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)


inline_for_extraction noextract
val eq_0_u64: a: uint64 -> r:bool{r == (uint_v a = 0)}

let eq_0_u64 a = eq_u64_nCT a (u64 0)



inline_for_extraction noextract
val unsafe_bool_of_u8 (x: uint8 { v x == 0 \/ v x == pow2 8 - 1 }):
  (b:bool { b <==> v x == 0 })

let unsafe_bool_of_u8 x = 
  match u8_to_UInt8 x with 
  | 0uy -> true
  | _ -> false


inline_for_extraction noextract
val unsafe_bool_of_u64 (x: uint64 { v x == 0 \/ v x == pow2 64 - 1 }):
  (b:bool { b <==> v x == 0 })

let unsafe_bool_of_u64 x = 
  match u64_to_UInt64 x with 
  | 0UL -> true
  | _ -> false


inline_for_extraction noextract
val unsafe_bool_of_u32 (x: uint32 { v x == 0 \/ v x == pow2 32 - 1 }):
  (b:bool { b <==> v x == 0 })

let unsafe_bool_of_u32 x = 
  let open FStar.UInt32 in 
  match u32_to_UInt32 x with 
  |0ul  -> true
  | _ -> false
