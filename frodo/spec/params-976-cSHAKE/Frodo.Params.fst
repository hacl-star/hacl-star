module Frodo.Params

open Lib.IntTypes

#reset-options "--max_fuel 0 --max_ifuel 0"

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

unfold let frodo_prf_spec = Spec.SHA3.cshake256_frodo

unfold let frodo_gen_matrix = Spec.Frodo.Gen.frodo_gen_matrix_cshake

val lemma_cdf_list:
  i:size_nat{i < List.Tot.length cdf_list}
  -> Lemma (uint_v (List.Tot.index cdf_list i) < pow2 15)
let lemma_cdf_list i =
  assert_norm (List.Tot.length cdf_list = 11);
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
  assert_norm (uint_v (List.Tot.index cdf_list 10) < pow2 15)
