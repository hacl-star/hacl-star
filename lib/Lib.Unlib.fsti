module Lib.Unlib

// A module of helpers to bring type equalities into scope while we wait for
// HACL* and the rest of the world to agree on a single secret integer type.

val reveal_secret8: unit -> Lemma
  (ensures (Lib.IntTypes.(uint_t U8 SEC) == UInt8.t))
