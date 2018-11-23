module Lib.RandomSequence

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


///
/// This module uses the OCaml cryptokit package to provide System randomness
///

val entropy: Type0


val crypto_random: len:size_nat -> Tot (option (lbytes len))

val crypto_random2: entropy -> len:size_nat -> Tot (entropy & lbytes len)

val crypto_random3: len:size_nat -> Tot (lbytes len)
