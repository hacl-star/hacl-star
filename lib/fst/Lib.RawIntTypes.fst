module Lib.RawIntTypes

open Lib.IntTypes

(* This module offers direct access to the internals of IntTypes.
   Typechecking it requires full access to IntTypes.fst (not just IntTypes.fsti)
   Use only if you need to, because using this module will load more F* dependencies.
   More importantly, using the u*_to_UInt* functions BREAKS secret independence.  *)

let u8_from_UInt8 x = x

let u16_from_UInt16 x = x

let u32_from_UInt32 x = x

let u64_from_UInt64 x = x

let u128_from_UInt128 x = x

let size_from_UInt32 x =  x

let u8_to_UInt8 x = x

let u16_to_UInt16 x = x

let u32_to_UInt32 x = x

let u64_to_UInt64 x = x

let u128_to_UInt128 x = x

let size_to_UInt32 x =  x

let uint_to_nat #t (x:uint_t t) =
  match t with
  | U8 -> UInt8.v x
  | U16 -> UInt16.v x
  | U32 -> UInt32.v x
  | U64 -> UInt64.v x
  | U128 -> UInt128.v x
  | SIZE -> UInt32.v x
  | NATm m -> x
