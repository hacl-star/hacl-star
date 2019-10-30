module Hacl.Hash.Core.SHA1

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

noextract inline_for_extraction
val legacy_alloca: alloca_st SHA1
val legacy_init: init_st SHA1
val legacy_update: update_st SHA1
val legacy_pad: pad_st SHA1
val legacy_finish: finish_st SHA1
