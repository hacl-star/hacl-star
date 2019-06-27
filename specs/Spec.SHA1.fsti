module Spec.SHA1

open Spec.Hash.Definitions

val init: init_t SHA1

val update: update_t SHA1

val pad: pad_t SHA1

val finish: finish_t SHA1
