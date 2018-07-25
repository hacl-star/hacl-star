module Spec.Frodo.Params

open Lib.IntTypes
open Lib.Sequence

module P = Hacl.Frodo.Params

let params_n = size_v P.params_n //640

let params_logq = size_v P.params_logq

let params_extracted_bits = size_v P.params_extracted_bits

let crypto_bytes = size_v P.crypto_bytes

let cdf_table_len = size_v P.cdf_table_len

let cdf_table: lseq uint16 cdf_table_len = Seq.createL P.cdf_table

let bytes_seed_a = size_v P.bytes_seed_a

let params_nbar = size_v P.params_nbar
