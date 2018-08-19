module Spec.Frodo.Params

open Lib.IntTypes
open Lib.Sequence

open Frodo.Params

unfold
let v = size_v

let params_n = v params_n

let params_logq = v params_logq

let params_extracted_bits = v params_extracted_bits

let crypto_bytes = v crypto_bytes

let cdf_table_len = v cdf_table_len

let cdf_table: lseq uint16 cdf_table_len = 
  assert_norm (List.Tot.length cdf_list == cdf_table_len);
  Seq.createL cdf_list

let bytes_seed_a = v bytes_seed_a

let params_nbar = v params_nbar

let cshake_frodo = Spec.Frodo.Keccak.cshake128_frodo

let frodo_gen_matrix = Spec.Frodo.Gen.frodo_gen_matrix_cshake
