module Frodo.Params

open Lib.IntTypes

unfold let params_n = size 640

unfold let params_logq = size 15

unfold let params_extracted_bits = size 2

unfold let crypto_bytes = size 16

unfold let cdf_table_len = size 12

unfold let cdf_list: list uint16 =
  [u16 4727;  u16 13584; u16 20864; u16 26113; u16 29434; u16 31278;
   u16 32176; u16 32560; u16 32704; u16 32751; u16 32764; u16 32767]

unfold let bytes_seed_a = size 16

unfold let params_nbar = size 8

unfold let frodo_prf_spec = Spec.SHA3.cshake128_frodo

unfold let frodo_gen_matrix = Spec.Frodo.Gen.frodo_gen_matrix_aes

val lemma_cdf_list:
  i:size_nat{i < List.Tot.length cdf_list}
  -> Lemma (uint_v (List.Tot.index cdf_list i) < pow2 15)
let lemma_cdf_list i =
  assert_norm (List.Tot.length cdf_list = 12);
  assert_norm (uint_v (List.Tot.index cdf_list 0) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list 1) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list 2) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list 3) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list 4) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list 5) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list 6) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list 7) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list 8) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list 9) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list 10) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list 11) < pow2 15)
