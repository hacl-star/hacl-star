module Spec.Lib.IntSeq.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

val create_index: #a:Type -> len:size_t -> init:a -> i:size_t{i < len} -> Lemma
		  (requires True)
		  (ensures (index (create len init) i == init))
		  [SMTPat (index (create len init) i)]

