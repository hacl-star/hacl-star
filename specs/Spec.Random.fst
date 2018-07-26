module Spec.Random

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


///
/// This module uses the OCaml cryptokit package to provide System randomness
///

assume val generate: len:size_nat -> Tot (lbytes len)
assume val write: len:size_nat -> lbytes len -> Tot bool
