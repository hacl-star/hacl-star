module Hacl.Impl.P256.LowLevel .RawCmp


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer


[@ (Comment "  This code is not side channel resistant")]

inline_for_extraction noextract
val eq_u8_nCT: a:uint8 -> b:uint8 -> (r:bool{r == (uint_v a = uint_v b)})

let eq_u8_nCT a b =
  let open Lib.RawIntTypes in
  FStar.UInt8.(u8_to_UInt8 a =^ u8_to_UInt8 b)


[@ (Comment "  This code is not side channel resistant")]

inline_for_extraction noextract
val eq_u64_nCT: a:uint64 -> b:uint64 -> (r:bool{r == (uint_v a = uint_v b)})

let eq_u64_nCT a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)


(* This code is not side channel resistant *)
inline_for_extraction noextract
val eq_0_u64: a: uint64 -> r:bool{r == (uint_v a = 0)}

let eq_0_u64 a = eq_u64_nCT a (u64 0)
