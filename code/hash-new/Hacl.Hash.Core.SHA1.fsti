module Hacl.Hash.Core.SHA1

open Hacl.Hash.Definitions
open Spec.Hash.Helpers

val alloca: alloca_st SHA1
val init: init_st SHA1
val update: update_st SHA1
val pad: pad_st SHA1
val finish: finish_st SHA1
