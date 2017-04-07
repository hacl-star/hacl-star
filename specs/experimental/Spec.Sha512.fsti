module Spec.Sha512

val sha512:
  input:Seq.seq UInt8.t{Seq.length input < pow2 32} ->
  Tot (hash:Seq.seq UInt8.t{Seq.length hash = 64})
