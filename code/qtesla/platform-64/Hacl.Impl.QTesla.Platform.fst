module Hacl.Impl.QTesla.Platform

open Hacl.Impl.QTesla.Params
open Hacl.Impl.QTesla.Globals

module I64 = FStar.Int64
module UI64 = FStar.UInt64

unfold let params_radix = 64
unfold let params_radix32 = 32
unfold let sdigit_t = I64.t
unfold let sdigit_n = I64.n
unfold let sdigit_v = I64.v
unfold let to_sdigit = I64.int_to_t
unfold let sdigit_to_int32 = FStar.Int.Cast.int64_to_int32
unfold let sdigit_to_int64 x = x
unfold let sdigit_to_elem = int64_to_elem
unfold let elem_to_sdigit = elem_to_int64
unfold let is_elem_sdigit = is_elem_i64
unfold let digit_t = UI64.t
unfold let digit_n = UI64.n
unfold let digit_inttype = Lib.IntTypes.U64
unfold let digit_to_sdigit = FStar.Int.Cast.uint64_to_int64
unfold let to_digit = UI64.uint_to_t

unfold let sdigit_op_Plus_Hat = I64.op_Plus_Hat
unfold let sdigit_op_Subtraction_Hat = I64.op_Subtraction_Hat
unfold let sdigit_op_Amp_Hat = I64.op_Amp_Hat
unfold let sdigit_op_Hat_Hat = I64.op_Hat_Hat
unfold let sdigit_op_Bar_Hat = I64.op_Bar_Hat
unfold let sdigit_op_Greater_Greater_Hat = I64.op_Greater_Greater_Hat
unfold let sdigit_op_Greater_Greater_Greater_Hat = I64.op_Greater_Greater_Greater_Hat
unfold let sdigit_op_Less_Hat = I64.op_Less_Hat
unfold let sdigit_lognot = I64.lognot
unfold let digit_lognot = UI64.lognot
unfold let digit_shift_right = UI64.shift_right

unfold let params_cdt_rows = params_cdt64_rows
unfold let params_cdt_cols = params_cdt64_cols
unfold let params_cdt_v = params_cdt64_v
