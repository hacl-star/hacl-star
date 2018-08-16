module Frodo.Params

open Lib.IntTypes

unfold let params_n = size 976

unfold let params_logq = size 16

unfold let params_extracted_bits = size 3

unfold let crypto_bytes = size 24

unfold let cdf_table_len = size 11

unfold let cdf_list: list uint16 = 
  [u16 5638;  u16 15915; u16 23689; u16 28571; u16 31116; u16 32217;
   u16 32613; u16 32731; u16 32760; u16 32766; u16 32767]

unfold let bytes_seed_a = size 16

unfold let params_nbar = size 8
