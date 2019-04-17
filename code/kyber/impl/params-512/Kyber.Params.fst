module Kyber.Params

open Lib.IntTypes

#reset-options "--max_fuel 0 --max_ifuel 0"

unfold let params_n = size 256

unfold let params_k = size 2

unfold let params_q = size 7681

unfold let params_eta = size 5

unfold let params_du = size 11

unfold let params_dv = size 3

unfold let params_dt = size 11

unfold let params_minus_log_delta = size 145

unfold let params_logr = size 18

unfold let params_qinv = size 7679
