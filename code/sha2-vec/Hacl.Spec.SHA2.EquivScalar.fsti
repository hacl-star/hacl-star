module Hacl.Spec.SHA2.EquivScalar

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Spec.Hash.Definitions
open Hacl.Spec.SHA2

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let max_size_t_lt_max_input_length (a:sha2_alg) : Lemma (max_size_t < max_input_length a) =
  Math.Lemmas.pow2_lt_compat 61 32;
  Math.Lemmas.pow2_lt_compat 125 32

val hash_lemma: #a:sha2_alg -> len:size_nat -> b:lseq uint8 len ->
  Lemma (max_size_t_lt_max_input_length a; hash #a len b == Spec.Agile.Hash.hash a b)
