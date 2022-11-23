module Spec.Blake2.Incremental

module S = FStar.Seq

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.Incremental.Definitions
open Spec.Hash.PadFinish
open Spec.Hash.Lemmas
open FStar.Mul

friend Spec.Agile.Hash

let blake2_is_hash_incremental a input =
  admit()
