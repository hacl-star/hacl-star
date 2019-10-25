module Spec.Frodo.Lemmas

open FStar.Mul

open Lib.IntTypes

val lemma_frodo_sample2:
    sign:uint16{uint_v sign == 0 \/ uint_v sign == 1}
  -> e:uint16{uint_v e < 12}
  -> Lemma (((lognot sign +. u16 1) ^. e) +. sign ==
           u16 ((Math.Lib.powx (-1) (uint_v sign) * uint_v e) % modulus U16))

val modulo_pow2_u16:
  a:uint16 -> b:size_nat{b < 16} -> Lemma
  (uint_v a % pow2 b == uint_v (a &. ((u16 1 <<. size b) -. u16 1)))

val modulo_pow2_u32:
  a:uint32 -> b:size_nat{b < 32} -> Lemma
  (uint_v a % pow2 b == uint_v (a &. ((u32 1 <<. size b) -. u32 1)))

val modulo_pow2_u64:
  a:uint64 -> b:size_nat{b < 64} -> Lemma
  (uint_v a % pow2 b == uint_v (a &. ((u64 1 <<. size b) -. u64 1)))

val lemma_mul_acc_comm:
  a:size_nat -> b:size_nat -> c:size_nat -> Lemma
  (a * b * c = c * a * b)

val lemma_matrix_index_repeati1:
  n1:size_nat -> n2:size_nat ->
  i:size_nat{i < n1} -> j:size_nat{j < n2} ->
  Lemma (2 * (i * n2 + j) + 2 <= 2 * n1 * n2)

val lemma_matrix_index_repeati2:
  n1:size_nat -> n2:size_nat ->
  i:size_nat{i < n1} -> j:size_nat{j < n2} ->
  Lemma (2 * (n1 * j + i) + 2 <= 2 * n1 * n2)

val lemma_matrix_index_repeati:
    n1:size_nat
  -> n2:size_nat{n1 * n2 <= max_size_t /\ n2 % 8 = 0}
  -> d:size_nat{d * n1 <= max_size_t /\ d * n1 * n2 / 8 <= max_size_t}
  -> i:size_nat{i < n1}
  -> j:size_nat{j < n2 / 8}
  -> Lemma (i * (n2 / 8) <= max_size_t /\
           i * (n2 / 8) + j <= max_size_t /\
           (i * (n2 / 8) + j) * d <= max_size_t /\
           (i * (n2 / 8) + j) * d + d <= d * n1 * n2 / 8)
