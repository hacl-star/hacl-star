module Spec.Hash.Incremental.Lemmas

module S = FStar.Seq

open Lib.IntTypes

open Spec.Hash.Definitions
open Spec.Agile.Hash
open Spec.Hash.PadFinish
open Spec.Hash.Incremental

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"
