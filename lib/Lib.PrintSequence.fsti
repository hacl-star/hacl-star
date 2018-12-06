module Lib.PrintSequence

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators



val print_nat8_hex: x:nat{x <= maxint U8} -> FStar.All.ML unit
val print_nat8_hex_pad: x:nat{x <= maxint U8} -> FStar.All.ML unit
val print_nat8_dec: x:nat{x <= maxint U8} -> FStar.All.ML unit
val print_nat8_dec_pad: x:nat{x <= maxint U8} -> FStar.All.ML unit

val print_nat32_hex: x:nat{x <= maxint U32} -> FStar.All.ML unit
val print_nat32_hex_pad: x:nat{x <= maxint U32} -> FStar.All.ML unit
val print_nat32_dec: x:nat{x <= maxint U32} -> FStar.All.ML unit
val print_nat32_dec_pad: x:nat{x <= maxint U32} -> FStar.All.ML unit

val print_nat64_hex: x:nat{x <= maxint U64} -> FStar.All.ML unit
val print_nat64_hex_pad: x:nat{x <= maxint U64} -> FStar.All.ML unit
val print_nat64_dec: x:nat{x <= maxint U64} -> FStar.All.ML unit
val print_nat64_dec_pad: x:nat{x <= maxint U64} -> FStar.All.ML unit


val print_uint8_hex: uint8 -> FStar.All.ML unit
val print_uint8_hex_pad: uint8 -> FStar.All.ML unit
val print_uint8_dec: uint8 -> FStar.All.ML unit
val print_uint8_dec_pad: uint8 -> FStar.All.ML unit

val print_uint32_hex: uint32 -> FStar.All.ML unit
val print_uint32_hex_pad: uint32 -> FStar.All.ML unit
val print_uint32_dec: uint32 -> FStar.All.ML unit
val print_uint32_dec_pad: uint32 -> FStar.All.ML unit

val print_uint64_hex: uint64 -> FStar.All.ML unit
val print_uint64_hex_pad: uint64 -> FStar.All.ML unit
val print_uint64_dec: uint64 -> FStar.All.ML unit
val print_uint64_dec_pad: uint64 -> FStar.All.ML unit


val print_label_nat64: string -> x:nat{x <= maxint U64} -> FStar.All.ML unit

val print_label_uint8: string -> uint8 -> FStar.All.ML unit
val print_label_uint32: string -> uint32 -> FStar.All.ML unit
val print_label_uint64: string -> uint64 -> FStar.All.ML unit


val print_list_nat64: list size_nat -> FStar.All.ML unit


val print_lbytes: #len:size_nat -> lbytes len -> FStar.All.ML unit
val print_label_lbytes: #len:size_nat -> string -> lbytes len -> FStar.All.ML unit

val print_compare: len:size_nat -> expected:lbytes len -> result:lbytes len -> FStar.All.ML bool
