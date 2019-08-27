// Common types and functions for heuristic parameter sets: I, III-size, III-speed
module Hacl.Impl.QTesla.Heuristic.Parameters

module I16 = FStar.Int16
module I32 = FStar.Int32
module UI32 = FStar.UInt32
open FStar.Int.Cast
open Lib.IntTypes

type elem_base = I32.t
type uelem_base = UI32.t
unfold let to_elem = I32.int_to_t
unfold let to_uelem = UI32.uint_to_t
module IElem = FStar.Int32
unfold let elem_n = IElem.n
unfold let elem_nbytes = numbytes U32
unfold let elem_v = IElem.v
unfold let uelem_v = UI32.v

unfold let elem_to_int8 = int32_to_int8
unfold let int8_to_elem = int8_to_int32
unfold let elem_to_uint8 x = Lib.RawIntTypes.u8_from_UInt8 (int32_to_uint8 x)
unfold let uint8_to_elem = uint8_to_int32
unfold let elem_to_int16 = int32_to_int16
unfold let int16_to_elem = int16_to_int32
unfold let elem_to_int32 (x:elem_base) : I32.t = x
unfold let int32_to_elem (x:I32.t) : elem_base = x
unfold let elem_to_uint32 = int32_to_uint32
unfold let uint32_to_elem = uint32_to_int32
unfold let elem_to_int64 = int32_to_int64
unfold let int64_to_elem = int64_to_int32
unfold let elem_to_uint64 = int32_to_uint64
unfold let uint64_to_elem = uint64_to_int32
unfold let elem_to_uelem = int32_to_uint32
unfold let uelem_to_elem = uint32_to_int32

unfold let uelem_sl = UI32.shift_left
unfold let uelem_sr = UI32.shift_right
unfold let uelem_or = UI32.logor

unfold let sparse_elem = I16.t
unfold let sparse_n = size I16.n
unfold let to_sparse_elem = I16.int_to_t
unfold let sparse_to_int16 (x:sparse_elem) : I16.t = x
unfold let sparse_v = I16.v

unfold let op_Plus_Hat = IElem.op_Plus_Hat
unfold let op_Subtraction_Hat = IElem.op_Subtraction_Hat
unfold let op_Star_Hat = IElem.op_Star_Hat
unfold let op_Slash_Hat = IElem.op_Slash_Hat
unfold let op_Percent_Hat = IElem.op_Percent_Hat
unfold let op_Hat_Hat = IElem.op_Hat_Hat
unfold let op_Amp_Hat = IElem.op_Amp_Hat
unfold let op_Bar_Hat = IElem.op_Bar_Hat
unfold let op_Less_Less_Hat = IElem.op_Less_Less_Hat
unfold let op_Less_Less_Less_Hat = Hacl.Impl.QTesla.ShiftArithmeticLeft.shift_arithmetic_left_i32
unfold let op_Greater_Greater_Hat = IElem.op_Greater_Greater_Hat
unfold let op_Greater_Greater_Greater_Hat = IElem.op_Greater_Greater_Greater_Hat
unfold let op_Equals_Hat = IElem.op_Equals_Hat
unfold let op_Greater_Hat = IElem.op_Greater_Hat
unfold let op_Greater_Equals_Hat = IElem.op_Greater_Equals_Hat
unfold let op_Less_Hat = IElem.op_Less_Hat
unfold let op_Less_Equals_Hat = IElem.op_Less_Equals_Hat
unfold let lognot = IElem.lognot

