module Lib.Random

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


///
/// This module uses the OCaml cryptokit package to provide System randomness
///

val crypto_random: len:size_nat -> Tot (option (lbytes len))
