module Hacl.Impl.QTesla.Platform

open Hacl.Impl.QTesla.Params

module I32 = FStar.Int32
module UI32 = FStar.UInt32

unfold let params_radix = 32
unfold let params_radix32 = 32
unfold let sdigit_t = I32.t
unfold let sdigit_n = I32.n
unfold let sdigit_v = I32.v
unfold let to_sdigit = I32.int_to_t
unfold let sdigit_to_int32 x = x
unfold let sdigit_to_int64 = FStar.Int.Cast.int32_to_int64
unfold let sdigit_to_elem = int32_to_elem
unfold let elem_to_sdigit = elem_to_int32
unfold let is_elem_sdigit = is_elem_i32
unfold let digit_t = UI32.t
unfold let digit_n = UI32.n
unfold let digit_inttype = Lib.IntTypes.U32
unfold let digit_to_sdigit = FStar.Int.Cast.uint32_to_int32
unfold let to_digit = UI32.uint_to_t

unfold let sdigit_op_Plus_Hat = I32.op_Plus_Hat
unfold let sdigit_op_Subtraction_Hat = I32.op_Subtraction_Hat
unfold let sdigit_op_Amp_Hat = I32.op_Amp_Hat
unfold let sdigit_op_Hat_Hat = I32.op_Hat_Hat
unfold let sdigit_op_Bar_Hat = I32.op_Bar_Hat
unfold let sdigit_op_Greater_Greater_Hat = I32.op_Greater_Greater_Hat
unfold let sdigit_op_Less_Hat = I32.op_Less_Hat
unfold let sdigit_lognot = I32.lognot
unfold let digit_lognot = UI32.lognot
unfold let digit_shift_right = UI32.shift_right

unfold let params_cdt_rows = params_cdt32_rows
unfold let params_cdt_cols = params_cdt32_cols
unfold let params_cdt_v = params_cdt32_v
