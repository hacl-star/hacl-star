module Lib.RawIntTypes

open Lib.IntTypes

(* This module offers direct access to the internals of IntTypes.
   Typechecking it requires full access to IntTypes.fst (not just IntTypes.fsti)
   Use only if you need to, because using this module will load more F* dependencies.
   More importantly, using the u*_to_UInt* functions BREAKS secret independence.  *)

inline_for_extraction
val u8_from_UInt8: (n:FStar.UInt8.t) -> u:uint8{uint_v #U8 u = UInt8.v n}
inline_for_extraction
val u16_from_UInt16: (n:FStar.UInt16.t) -> u:uint16{uint_v #U16 u = UInt16.v n}
inline_for_extraction
val u32_from_UInt32: (n:FStar.UInt32.t) -> u:uint32{uint_v #U32 u = UInt32.v n}
inline_for_extraction
val u64_from_UInt64: (n:FStar.UInt64.t) -> u:uint64{uint_v #U64 u = UInt64.v n}
inline_for_extraction
val u128_from_UInt128: (n:FStar.UInt128.t) -> u:uint128{uint_v #U128 u = UInt128.v n}
inline_for_extraction
val size_from_UInt32: (n:FStar.UInt32.t) -> u:size_t{uint_v  u = UInt32.v n}

inline_for_extraction
val u8_to_UInt8: (u:uint8) -> n:UInt8.t{uint_v #U8 u = UInt8.v n}
inline_for_extraction
val u16_to_UInt16: (u:uint16) -> n:UInt16.t{uint_v #U16 u = UInt16.v n}
inline_for_extraction
val u32_to_UInt32: (u:uint32) -> n:UInt32.t{uint_v #U32 u = UInt32.v n}
inline_for_extraction
val u64_to_UInt64: (u:uint64) -> n:UInt64.t{uint_v #U64 u = UInt64.v n}
inline_for_extraction
val u128_to_UInt128: (u:uint128) -> n:UInt128.t{uint_v #U128 u = UInt128.v n}
inline_for_extraction
val size_to_UInt32: (u:size_t) -> n:UInt32.t{uint_v  u = UInt32.v n}

inline_for_extraction
val uint_to_nat: #t:inttype{unsigned t} -> #l:secrecy_level -> u:uint_t t l -> n:nat{n = uint_v #t u}
