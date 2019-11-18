module Spec.SHA2.Lemmas

open Spec.Hash.Definitions

val update_224_256: hash:words_state SHA2_256 ->
  block:bytes{Seq.length block = block_length SHA2_256} ->
  Lemma
    (ensures (Spec.SHA2.(update SHA2_256 hash block == update SHA2_224 hash block)))

val update_multi_224_256: hash:words_state SHA2_256 -> blocks:bytes_blocks SHA2_256 ->
  Lemma
    (ensures (Spec.Agile.Hash.update_multi SHA2_256 hash blocks ==
      Spec.Agile.Hash.update_multi SHA2_224 hash blocks))
    (decreases (Seq.length blocks))
