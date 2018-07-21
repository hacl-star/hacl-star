module Spec.Frodo.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RawIntTypes
open FStar.Math.Lemmas

open Spec.PQ.Lib

#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 0 --z3seed 2"

val modulo_pow2_u16:
  a:uint16 -> b:size_nat{b < 16} -> Lemma
  (uint_v a % pow2 b == uint_v (a &. ((u16 1 <<. u32 b) -. u16 1)))
let modulo_pow2_u16 a b =
  uintv_extensionality (nat_to_uint 1) (u16 1);
  mod_mask_lemma #U16 a (u32 b)

val modulo_pow2_u64:
  a:uint64 -> b:size_nat{b < 64} -> Lemma
  (uint_v a % pow2 b == uint_v (a &. ((u64 1 <<. u32 b) -. u64 1)))
let modulo_pow2_u64 a b =
  uintv_extensionality (nat_to_uint 1) (u64 1);
  mod_mask_lemma #U64 a (u32 b)

val lemma_mul_acc_comm:
  a:size_nat -> b:size_nat -> c:size_nat -> Lemma
  (a * b * c = c * a * b)
let lemma_mul_acc_comm a b c = ()

val lemma_matrix_index_repeati:
  n1:size_nat -> n2:size_nat{n2 % 8 = 0} ->
  d:size_nat{d * n1 * n2 / 8 < max_size_t} ->
  i:size_nat{i < n1} -> j:size_nat{j < n2 / 8} ->
  Lemma ((i * n2 / 8 + j) * d + d <= d * n1 * n2 / 8)
let lemma_matrix_index_repeati n1 n2 d i j =
  let res = (i * n2 / 8 + j) * d + d in
  assert (i * n2 / 8 + j <= (n1 - 1) * n2 / 8 + n2 / 8 - 1);
  //assert ((n1 - 1) * n2 / 8 = n1 * n2 / 8 - n2 / 8);
  assert ((n1 - 1) * n2 / 8 + n2 / 8 - 1 = n1 * n2 / 8 - 1);
  lemma_mult_le_right d (i * n2 / 8 + j) (n1 * n2 / 8 - 1);
  assert ((i * n2 / 8 + j) * d <= (n1 * n2 / 8 - 1) * d);
  assert (res <= (n1 * n2 / 8 - 1) * d + d);
  assert ((n1 * n2 / 8 - 1) * d + d = n1 * n2 / 8 * d - d + d)

val lemma_matrix_index_repeati1:
  n1:size_nat -> n2:size_nat ->
  i:size_nat{i < n1} -> j:size_nat{j < n2} ->
  Lemma (2 * (i * n2 + j) + 2 <= 2 * n1 * n2)
let lemma_matrix_index_repeati1 n1 n2 i j =
  assert (2 * (i * n2 + j) + 2 <= 2 * ((n1 - 1) * n2 + n2 - 1) + 2);
  assert (2 * (n1 * n2 - 1) + 2 = 2 * n1 * n2 - 2 + 2);
  assert (2 * (i * n2 + j) + 2 <= 2 * n1 * n2)

val lemma_matrix_index_repeati2:
  n1:size_nat -> n2:size_nat ->
  i:size_nat{i < n1} -> j:size_nat{j < n2} ->
  Lemma (2 * (n1 * j + i) + 2 <= 2 * n1 * n2)
let lemma_matrix_index_repeati2 n1 n2 i j =
  assert (2 * (n1 * j + i) + 2 <= 2 * (n1 * (n2 - 1) + n1 - 1) + 2);
  assert (2 * (n1 * n2 - 1) + 2 = 2 * n1 * n2 - 2 + 2);
  assert (2 * (n1 * j + i) + 2 <= 2 * n1 * n2)

// val ec:k:size_nat{k < pow2 params_extracted_bits} -> Tot (r:size_nat{r < pow2 params_logq})
// let ec k = k * pow2 (params_logq - params_extracted_bits)

// val dc:c:size_nat{c < pow2 params_logq} -> Tot (r:size_nat{r < pow2 params_extracted_bits})
// let dc c = ((c + pow2 (params_logq - params_extracted_bits - 1)) / pow2 (params_logq - params_extracted_bits)) % pow2 params_extracted_bits

// val lemma_dc_ec:
//   k:size_nat{k < pow2 params_extracted_bits} -> Lemma (dc (ec k) == k)
// let lemma_dc_ec k =
//   let c = ec k in
//   assert (c == k * pow2 (params_logq - params_extracted_bits));
//   assert (dc c == ((c + pow2 (params_logq - params_extracted_bits - 1)) / pow2 (params_logq - params_extracted_bits)) % pow2 params_extracted_bits);
//   assert (dc c == ((k * pow2 (params_logq - params_extracted_bits) + pow2 (params_logq - params_extracted_bits - 1)) / pow2 (params_logq - params_extracted_bits)) % pow2 params_extracted_bits);
//   pow2_plus 1 (params_logq - params_extracted_bits - 1);
//   //assert (pow2 (params_logq - params_extracted_bits) = pow2 1 * pow2 (params_logq - params_extracted_bits - 1));
//   distributivity_add_left (k * pow2 1) 1 (pow2 (params_logq - params_extracted_bits - 1));
//   //assert (dc c == (((k * pow2 1 + 1) * pow2 (params_logq - params_extracted_bits - 1)) / (pow2 1 * pow2 (params_logq - params_extracted_bits - 1))) % pow2 params_extracted_bits);
//   division_multiplication_lemma ((k * pow2 1 + 1) * pow2 (params_logq - params_extracted_bits - 1))  (pow2 (params_logq - params_extracted_bits - 1)) (pow2 1);
//   //assert (dc c == (((k * pow2 1 + 1) * pow2 (params_logq - params_extracted_bits - 1)) /  pow2 (params_logq - params_extracted_bits - 1) / pow2 1) % pow2 params_extracted_bits);
//   multiple_division_lemma (k * pow2 1 + 1) (pow2 (params_logq - params_extracted_bits - 1));
//   //assert (dc c == ((k * pow2 1 + 1) / pow2 1) % pow2 params_extracted_bits);
//   division_addition_lemma 1 (pow2 1) k;
//   //assert (dc c == (k + 1 / pow2 1) % pow2 params_extracted_bits);
//   small_division_lemma_1 1 (pow2 1);
//   small_modulo_lemma_1 k (pow2 params_extracted_bits)
