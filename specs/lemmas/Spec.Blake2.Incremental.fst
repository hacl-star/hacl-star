module Spec.Blake2.Incremental

module S = FStar.Seq

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.Incremental.Definitions
open Spec.Hash.PadFinish
open Spec.Hash.Lemmas
open FStar.Mul

friend Spec.Agile.Hash

// TODO: move or reuse currently located in Hacl.Streaming.Blake2
let blake2_is_hash_incremental a input =
  admit ()

