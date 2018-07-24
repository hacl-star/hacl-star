module Hacl.Impl.Frodo.Params

open Lib.IntTypes
open Lib.PQ.Buffer

module S = Spec.Frodo.Params

let params_n: r:size_t{v r = S.params_n} = size 64 // 640

let params_logq: r:size_t{v r = S.params_logq} = size 15

let params_extracted_bits: r:size_t{v r = S.params_extracted_bits} = size 2

let crypto_bytes: r:size_t{v r = S.crypto_bytes} = size 16

let cdf_table_len: r:size_t{v r = S.cdf_table_len} = size 12

let cdf_table: b:lbuffer uint16 (v cdf_table_len) { LowStar.Buffer.recallable b } =
  LowStar.Buffer.gcmalloc_of_list HyperStack.root
    [u16 4727; u16 13584; u16 20864; u16 26113; u16 29434; u16 31278;
     u16 32176; u16 32560; u16 32704; u16 32751; u16 32764; u16 32767]

let bytes_seed_a: r:size_t{v r = S.bytes_seed_a} = size 16

let params_nbar:r:size_t{v r = S.params_nbar} = size 8
