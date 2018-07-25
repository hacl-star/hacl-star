module Hacl.Impl.Frodo.Params

open Lib.IntTypes
open Lib.PQ.Buffer

module P = Hacl.Frodo.Params

let params_n = P.params_n // 640

let params_logq = P.params_logq

let params_extracted_bits = P.params_extracted_bits

let crypto_bytes = P.crypto_bytes

let cdf_table_len = P.cdf_table_len

let cdf_table: b:lbuffer uint16 (v cdf_table_len) { LowStar.Buffer.recallable b } =
  LowStar.Buffer.gcmalloc_of_list HyperStack.root P.cdf_table

let bytes_seed_a = P.bytes_seed_a

let params_nbar = P.params_nbar
