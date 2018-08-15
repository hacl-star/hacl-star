module Spec.SHA2

open Spec.Hash.Helpers

val init: a:hash_alg -> init_t a

val update: a: hash_alg -> update_t a

val pad: a:hash_alg -> pad_t a

val finish: a:hash_alg -> finish_t a
