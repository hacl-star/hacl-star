module Spec.Kyber2.Lemmas

open FStar.Mul
open FStar.Math.Lemmas

open Lib.IntTypes

friend Lib.IntTypes

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let modulo_plus_minus a n =
  let b = a % n in
  if b > n/2 then b - n else b

let lemma_mod_plus_minus_injective n a p =
  ()

let lemma_mod_plus_minus_opposite n a =
  ()
  
let modulo_pow2_u16 a b =
  mod_mask_lemma #U16 a (UInt32.uint_to_t b)

let modulo_pow2_u32 a b =
  mod_mask_lemma #U32 a (UInt32.uint_to_t b)

let modulo_pow2_pub_u32 a b =
  mod_mask_lemma #U32 #PUB a (UInt32.uint_to_t b)

let modulo_pow2_u64 a b =
  mod_mask_lemma #U64 a (UInt32.uint_to_t b)

let lemma_mul_acc_comm a b c = ()

let lemma_matrix_index_repeati1 n1 n2 i j =
  assert (i * n2 + j <= (n1 - 1) * n2 + (n2 - 1));
  assert (2 * (i * n2 + j) + 2 <= 2 * ((n1 - 1) * n2 + (n2 - 1)) + 2);
  assert (2 * ((n1 - 1) * n2 + (n2 - 1)) + 2 = 2 * (n1 - 1) * n2 + 2 * n2 - 2 + 2);
  assert (2 * (n1 - 1) * n2 + 2 * n2 - 2 + 2 = 2 * n1 * n2)

let lemma_matrix_index_repeati2 n1 n2 i j =
  assert (2 * (n1 * j + i) + 2 <= 2 * (n1 * (n2 - 1) + n1 - 1) + 2);
  assert (2 * (n1 * n2 - 1) + 2 = 2 * n1 * n2 - 2 + 2)

let lemma_matrix_index_repeati n1 n2 d i j =
  assert (i * (n2 / 8) + j <= (n1 - 1) * (n2 / 8) + (n2 / 8 - 1));
  lemma_mult_le_right d (i * (n2 / 8) + j) (n1 * (n2 / 8) - 1)
