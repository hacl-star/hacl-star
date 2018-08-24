module Lib.Endianness

open FStar.HyperStack
open FStar.HyperStack.ST

open LowStar.Buffer

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.PQ.Buffer

module B = LowStar.Buffer
module ByteSeq = Lib.ByteSequence

friend Lib.IntTypes

// TODO: Fix this
#set-options "--admit_smt_queries true"

let uint_from_bytes_le #t i =
  match t with
  | U8 -> i.(size 0)
  | U16 -> let u = C.load16_le i in u16_from_UInt16 u
  | U32 -> let u = C.load32_le i in u32_from_UInt32 u
  | U64 -> let u = C.load64_le i in u64_from_UInt64 u
  | U128 -> let u = C.load128_le i in u128_from_UInt128 u

let uint_from_bytes_be #t i =
  match t with
  | U8 -> i.(size 0)
  | U16 -> let u = C.load16_be i in u16_from_UInt16 u
  | U32 -> let u = C.load32_be i in u32_from_UInt32 u
  | U64 -> let u = C.load64_be i in u64_from_UInt64 u
  | U128 -> let u = C.load128_be i in u128_from_UInt128 u

let uint_to_bytes_le #t o i =
  match t with
  | U8 -> o.(size 0) <- i
  | U16 -> C.store16_le o (u16_to_UInt16 i)
  | U32 -> C.store32_le o (u32_to_UInt32 i)
  | U64 -> C.store64_le o (u64_to_UInt64 i)
  | U128 -> C.store128_le o (u128_to_UInt128 i)

let uint_to_bytes_be #t o i =
  match t with
  | U8 -> o.(size 0) <- i
  | U16 -> C.store16_be o (u16_to_UInt16 i)
  | U32 -> C.store32_be o (u32_to_UInt32 i)
  | U64 -> C.store64_be o (u64_to_UInt64 i)
  | U128 -> C.store128_be o (u128_to_UInt128 i)
