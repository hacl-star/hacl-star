module Frodo.Params

open Lib.IntTypes

unfold let params_n = size 64 // 640

unfold let params_logq = size 15

unfold let params_extracted_bits = size 2

unfold let crypto_bytes = size 16

unfold let cdf_table_len = size 12

unfold let cdf_list: list uint16 = 
  [u16 4727;  u16 13584; u16 20864; u16 26113; u16 29434; u16 31278;
   u16 32176; u16 32560; u16 32704; u16 32751; u16 32764; u16 32767]

unfold let bytes_seed_a = size 16

unfold let params_nbar = size 8
