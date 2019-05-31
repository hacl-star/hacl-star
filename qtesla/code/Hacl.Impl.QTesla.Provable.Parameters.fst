// Common types and functions for provable parameter sets: p-I and p-III
module Hacl.Impl.QTesla.Provable.Parameters

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

module I8 = FStar.Int8
module I16 = FStar.Int16
module I64 = FStar.Int64
module UI64 = FStar.UInt64
open FStar.Int.Cast
open Lib.IntTypes

type elem_base = I64.t
type uelem_base = UI64.t
unfold let to_elem = I64.int_to_t
unfold let to_uelem = UI64.uint_to_t
module IElem = FStar.Int64
unfold let elem_n = IElem.n
unfold let elem_nbytes = numbytes U64
unfold let elem_v = IElem.v
unfold let uelem_v = UI64.v

unfold let elem_to_int8 = int64_to_int8
unfold let int8_to_elem = int8_to_int64
unfold let elem_to_uint8 = int64_to_uint8
unfold let uint8_to_elem = uint8_to_int64
unfold let elem_to_int16 = int64_to_int16
unfold let int16_to_elem = int16_to_int64
unfold let elem_to_int32 = int64_to_int32
unfold let int32_to_elem = int32_to_int64
unfold let elem_to_uint32 = int64_to_uint32
unfold let uint32_to_elem = uint32_to_int64
unfold let elem_to_int64 (x:elem_base) : I64.t = x
unfold let int64_to_elem (x:I64.t) : elem_base = x
unfold let elem_to_uint64 = int64_to_uint64
unfold let uint64_to_elem = uint64_to_int64
unfold let elem_to_uelem = int64_to_uint64
unfold let uelem_to_elem = uint64_to_int64

unfold let uelem_sl = UI64.shift_left
unfold let uelem_sr = UI64.shift_right
unfold let uelem_or = UI64.logor

unfold let sparse_elem = I8.t
unfold let sparse_n = I8.n
unfold let to_sparse_elem = I8.int_to_t
unfold let sparse_to_int16 = int8_to_int16
unfold let sparse_v = I8.v

unfold let op_Plus_Hat = IElem.op_Plus_Hat
unfold let op_Subtraction_Hat = IElem.op_Subtraction_Hat
unfold let op_Star_Hat = IElem.op_Star_Hat
unfold let op_Slash_Hat = IElem.op_Slash_Hat
unfold let op_Percent_Hat = IElem.op_Percent_Hat
unfold let op_Hat_Hat = IElem.op_Hat_Hat
unfold let op_Amp_Hat = IElem.op_Amp_Hat
unfold let op_Bar_Hat = IElem.op_Bar_Hat
unfold let op_Less_Less_Hat = IElem.op_Less_Less_Hat
unfold let op_Greater_Greater_Hat = IElem.op_Greater_Greater_Hat
unfold let op_Greater_Greater_Greater_Hat = IElem.op_Greater_Greater_Greater_Hat
unfold let op_Equals_Hat = IElem.op_Equals_Hat
unfold let op_Greater_Hat = IElem.op_Greater_Hat
unfold let op_Greater_Equals_Hat = IElem.op_Greater_Equals_Hat
unfold let op_Less_Hat = IElem.op_Less_Hat
unfold let op_Less_Equals_Hat = IElem.op_Less_Equals_Hat
unfold let lognot = IElem.lognot

