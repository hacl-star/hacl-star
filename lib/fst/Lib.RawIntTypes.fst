module Lib.RawIntTypes

open Lib.IntTypes

(* This module offers direct access to the internals of IntTypes.
   Typechecking it requires full access to IntTypes.fst (not just IntTypes.fsti)
   Use only if you need to, because using this module will load more F* dependencies.
   More importantly, using the u*_to_UInt* functions BREAKS secret independence.  *)

let u8_from_UInt8 x = u8 (UInt8.v x)

let u16_from_UInt16 x = u16 (UInt16.v x)

let u32_from_UInt32 x = u32 (UInt32.v x)

let u64_from_UInt64 x = u64 (UInt64.v x)

let u128_from_UInt128 x = u128 (UInt128.v x)

let size_from_UInt32 x = x

let u8_to_UInt8 x = UInt8.uint_to_t (uint_v x)

let u16_to_UInt16 x = UInt16.uint_to_t (uint_v x)

let u32_to_UInt32 x = UInt32.uint_to_t (uint_v x)

let u64_to_UInt64 x = UInt64.uint_to_t (uint_v x)

let u128_to_UInt128 x = UInt128.uint_to_t (uint_v x)

let size_to_UInt32 x = x

let uint_to_nat #t #l (x:uint_t t l) = uint_v #t #l x
