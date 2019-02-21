module Hacl.Hash.Core.MD5

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

noextract inline_for_extraction
val alloca: alloca_st MD5
val init: init_st MD5
val update: update_st MD5
val pad: pad_st MD5
val finish: finish_st MD5
