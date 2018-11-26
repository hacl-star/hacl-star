module Lib.PrintSequence

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators


val print_lbytes: #len:size_nat -> lbytes len -> FStar.All.ML unit

val print_hex_uint8: uint8 -> FStar.All.ML unit
val print_hex_uint32: uint32 -> FStar.All.ML unit
val print_hex_uint64: uint64 -> FStar.All.ML unit

val print_dec_uint8: uint8 -> FStar.All.ML unit
val print_dec_uint32: uint32 -> FStar.All.ML unit
val print_dec_uint64: uint64 -> FStar.All.ML unit

val print_hex_nat8: x:nat{x <= maxint U8} -> FStar.All.ML unit
val print_hex_nat32: x:nat{x <= maxint U32} -> FStar.All.ML unit
val print_hex_nat64: x:nat{x <= maxint U64} -> FStar.All.ML unit

val print_dec_nat8: x:nat{x <= maxint U8} -> FStar.All.ML unit
val print_dec_nat32: x:nat{x <= maxint U32} -> FStar.All.ML unit
val print_dec_nat64: x:nat{x <= maxint U64} -> FStar.All.ML unit

val print_label_hex_uint8: string -> uint8 -> FStar.All.ML unit
val print_label_hex_uint32: string -> uint32 -> FStar.All.ML unit
val print_label_hex_uint64: string -> uint64 -> FStar.All.ML unit

val print_label_dec_nat8: string -> x:nat{x <= maxint U8} -> FStar.All.ML unit
val print_label_dec_nat32: string -> x:nat{x <= maxint U32} -> FStar.All.ML unit
val print_label_dec_nat64: string -> x:nat{x <= maxint U64} -> FStar.All.ML unit

val print_compare: len:size_nat -> expected:lbytes len -> result:lbytes len -> FStar.All.ML bool
