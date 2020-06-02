module Hacl.Spec.SHA2.EquivScalar

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Spec.Hash.Definitions
open Hacl.Spec.SHA2

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val hash_agile_lemma: #a:sha2_alg -> len:size_nat{len <= max_input_length a} -> b:lseq uint8 len ->
  Lemma (hash #a len b == Spec.Agile.Hash.hash a b)
