module Spec.Hash.Incremental.Lemmas

module S = FStar.Seq

open Spec.Hash.Definitions
open Spec.Agile.Hash
open Spec.Hash.PadFinish
open Spec.Hash.Incremental

val concatenated_hash_incremental (a:hash_alg) (inp1:bytes_blocks a) (inp2:bytes)
  : Lemma
    (requires Seq.length (inp1 `S.append` inp2) <= max_input_length a /\ Seq.length inp2 > 0)
    (ensures finish a (update_last a (update_multi a (init a) inp1) (S.length inp1) inp2)
      `S.equal` hash_incremental a (inp1 `S.append` inp2))
