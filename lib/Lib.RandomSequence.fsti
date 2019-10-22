module Lib.RandomSequence

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


///
/// This module uses the OCaml cryptokit package to provide Hardware randomness
/// (Currently only usable from platforms that support RDRAND)
///

val entropy: Type0
val entropy0: entropy


val crypto_random: entropy -> len:size_nat -> Tot (entropy & lbytes len)

val unsound_crypto_random1: len:size_nat -> Tot (option (lbytes len))

val unsound_crypto_random2: len:size_nat -> Tot (lbytes len)
