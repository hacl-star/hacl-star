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


val print_label_nat64: display:bool -> string -> x:nat{x <= maxint U64} -> FStar.All.ML unit

val print_label_uint8: display:bool -> string -> uint8 -> FStar.All.ML unit
val print_label_uint32: display:bool -> string -> uint32 -> FStar.All.ML unit
val print_label_uint64: display:bool -> string -> uint64 -> FStar.All.ML unit


val print_list_nat64: display:bool -> list size_nat -> FStar.All.ML unit

val print_string: display:bool -> string -> FStar.All.ML unit
val print_lbytes: display:bool -> len:size_nat -> lbytes len -> FStar.All.ML unit
val print_label_lbytes: display:bool -> string -> len:size_nat -> lbytes len -> FStar.All.ML unit

val print_compare: display:bool -> len:size_nat -> expected:lbytes len -> result:lbytes len -> FStar.All.ML bool
val print_compare_display: display:bool -> len:size_nat -> expected:lbytes len -> result:lbytes len -> FStar.All.ML bool
val print_compare_display_diff: display:bool -> len:size_nat -> expected:lbytes len -> result:lbytes len -> FStar.All.ML bool
val print_label_compare_display: display:bool -> s:string -> len:size_nat -> expected:lbytes len -> result:lbytes len -> FStar.All.ML bool
val print_label_compare_display_diff: display:bool -> s:string -> len:size_nat -> expected:lbytes len -> result:lbytes len -> FStar.All.ML bool
