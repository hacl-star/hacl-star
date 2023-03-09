module Spec.SHA2.Lemmas

open Spec.Hash.Definitions

#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"

val update_224_256: st:words_state SHA2_256 ->
  block:bytes{Seq.length block = block_length SHA2_256} ->
  Lemma
    (ensures (Spec.Agile.Hash.(update SHA2_256 st block == update SHA2_224 st block)))

val update_multi_224_256: hash:words_state SHA2_256 -> blocks:bytes_blocks SHA2_256 ->
  Lemma
    (ensures (Spec.Agile.Hash.update_multi SHA2_256 hash () blocks ==
      Spec.Agile.Hash.update_multi SHA2_224 hash () blocks))
    (decreases (Seq.length blocks))

val update_last_224_256:
  hash:words_state SHA2_256 ->
  prevlen:Spec.Hash.Incremental.Definitions.prev_length_t SHA2_256 ->
  input:bytes{ (Seq.length input + prevlen) `less_than_max_input_length` SHA2_256 /\
    Seq.length input <= block_length SHA2_256 } ->
  Lemma
    (ensures Spec.Hash.Incremental.Definitions.update_last SHA2_256 hash prevlen input ==
      Spec.Hash.Incremental.Definitions.update_last SHA2_224 hash prevlen input)


val update_384_512: st:words_state SHA2_512 ->
  block:bytes{Seq.length block = block_length SHA2_512} ->
  Lemma
    (ensures (Spec.Agile.Hash.(update SHA2_512 st block == update SHA2_384 st block)))

val update_multi_384_512: hash:words_state SHA2_512 -> blocks:bytes_blocks SHA2_512 ->
  Lemma
    (ensures (Spec.Agile.Hash.update_multi SHA2_512 hash () blocks ==
      Spec.Agile.Hash.update_multi SHA2_384 hash () blocks))
    (decreases (Seq.length blocks))

val update_last_384_512:
  hash:words_state SHA2_512 ->
  prevlen:Spec.Hash.Incremental.Definitions.prev_length_t SHA2_512 ->
  input:bytes{ (Seq.length input + prevlen) `less_than_max_input_length` SHA2_512 /\
    Seq.length input <= block_length SHA2_512 } ->
  Lemma
    (ensures Spec.Hash.Incremental.Definitions.update_last SHA2_512 hash prevlen input ==
      Spec.Hash.Incremental.Definitions.update_last SHA2_384 hash prevlen input)
