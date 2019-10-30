module Hacl.Hash.Core.MD5

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

noextract inline_for_extraction
val legacy_alloca: alloca_st MD5
val legacy_init: init_st MD5
val legacy_update: update_st MD5
val legacy_pad: pad_st MD5
val legacy_finish: finish_st MD5
