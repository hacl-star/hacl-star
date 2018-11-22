module Lib.PrintSequence

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators


val print_lbytes: #len:size_nat -> lbytes len -> FStar.All.ML unit

val print_uint8: uint8 -> FStar.All.ML unit
val print_uint32: uint32 -> FStar.All.ML unit
val print_uint64: uint64 -> FStar.All.ML unit

val print_nat8: x:nat{x <= maxint U8} -> FStar.All.ML unit
val print_nat32: x:nat{x <= maxint U32} -> FStar.All.ML unit
val print_nat64: x:nat{x <= maxint U64} -> FStar.All.ML unit

val print_label_uint8: string -> uint8 -> FStar.All.ML unit
val print_label_uint32: string -> uint32 -> FStar.All.ML unit
val print_label_uint64: string -> uint64 -> FStar.All.ML unit

val print_label_nat8: string -> x:nat{x <= maxint U8} -> FStar.All.ML unit
val print_label_nat32: string -> x:nat{x <= maxint U32} -> FStar.All.ML unit
val print_label_nat64: string -> x:nat{x <= maxint U64} -> FStar.All.ML unit

val print_compare: len:size_nat -> expected:lbytes len -> result:lbytes len -> FStar.All.ML bool
