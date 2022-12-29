module Hacl.Hash.SHA2

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

include Hacl.Hash.Core.SHA2

val update_multi_224: update_multi_st (|SHA2_224, ()|)
val update_multi_256: update_multi_st (|SHA2_256, ()|)
val update_multi_384: update_multi_st (|SHA2_384, ()|)
val update_multi_512: update_multi_st (|SHA2_512, ()|)

val update_last_224: update_last_st (|SHA2_224, ()|)
val update_last_256: update_last_st (|SHA2_256, ()|)
val update_last_384: update_last_st (|SHA2_384, ()|)
val update_last_512: update_last_st (|SHA2_512, ()|)

val hash_224: hash_st SHA2_224
val hash_256: hash_st SHA2_256
val hash_384: hash_st SHA2_384
val hash_512: hash_st SHA2_512
