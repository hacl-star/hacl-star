module Hacl.Impl.Hash.Reveal

open Lib.Sequence
open Lib.ByteSequence

val reveal_agile_sha512
  (b:bytes{length b <= Spec.Agile.Hash.max_input Spec.Agile.Hash.HASH_SHA2_512}) : Lemma
  (Spec.Agile.Hash.hash Spec.Agile.Hash.HASH_SHA2_512 b ==
    Spec.Hash.hash Spec.Hash.Definitions.SHA2_512 b)
