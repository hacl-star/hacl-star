module Spec.MD5

open Spec.Hash.Definitions

val init: init_t MD5

val update: update_t MD5

val pad: pad_t MD5

val finish: finish_t MD5
