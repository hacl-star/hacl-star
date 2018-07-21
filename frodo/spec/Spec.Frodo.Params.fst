module Spec.Frodo.Params

open Lib.IntTypes
open Lib.Sequence

let params_n: size_nat = 64 //640

let params_logq: size_nat = 15

let params_extracted_bits: size_nat = 2

let crypto_bytes: size_nat = 16

let cdf_table_len: size_nat = 12

let cdf_table: lseq size_nat cdf_table_len =
  let cdf_table0: list size_nat =
    [4727; 13584; 20864; 26113; 29434; 31278; 32176; 32560; 32704; 32751; 32764; 32767] in
  assert_norm (List.Tot.length cdf_table0 == cdf_table_len);
  Seq.createL cdf_table0

let bytes_seed_a: size_nat = 16

let params_nbar: size_nat = 8
