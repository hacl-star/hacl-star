module Spec.SHA2

open Spec.Hash.Definitions

val init: a:sha2_alg -> init_t a

val update: a:sha2_alg -> update_t a
