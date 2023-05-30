module Hacl.Streaming.Blake2s_128

module G = FStar.Ghost
module F = Hacl.Streaming.Functor

module Spec = Spec.Blake2
open Hacl.Impl.Blake2.Core
open Hacl.Streaming.Blake2
module Blake2s128 = Hacl.Blake2s_128

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

/// The functor
inline_for_extraction noextract
let blake2s_128 kk = blake2_index Spec.Blake2S M128 kk

/// Type abbreviations
let blake2s_128_block_state = s Spec.Blake2S M128
let blake2s_128_state = F.state_s (blake2s_128 0) (s Spec.Blake2S M128) (empty_key Spec.Blake2S)

/// No key
inline_for_extraction noextract
let blake2s_128_no_key_alloca : F.alloca_st (blake2s_128 0) =
  F.mk_alloca #(blake2s_128 0)
    (blake2_init Spec.Blake2S M128 0 Blake2s128.blake2s_init)
    (key_copy Spec.Blake2S 0)
    (key_alloca Spec.Blake2S 0)
    (state_alloca Spec.Blake2S M128)

[@ (Comment "  Copy function when there is no key")]
let blake2s_128_no_key_copy : F.copy_st (blake2s_128 0) =
  F.mk_copy #(blake2s_128 0)
    (key_copy Spec.Blake2S 0)
    (key_create_in Spec.Blake2S 0)
    (state_copy Spec.Blake2S M128)
    (state_create_in Spec.Blake2S M128)

[@ (Comment "  State allocation function when there is no key")]
let blake2s_128_no_key_create_in : F.create_in_st (blake2s_128 0) =
  F.mk_create_in #(blake2s_128 0)
    (blake2_init Spec.Blake2S M128 0 Blake2s128.blake2s_init)
    (key_copy Spec.Blake2S 0)
    (key_create_in Spec.Blake2S 0)
    (state_create_in Spec.Blake2S M128)

[@ (Comment "  (Re-)initialization function when there is no key")]
let blake2s_128_no_key_init : F.init_st (blake2s_128 0) =
  F.mk_init #(blake2s_128 0)
    (key_copy Spec.Blake2S 0)
    (blake2_init Spec.Blake2S M128 0 Blake2s128.blake2s_init)

[@ (Comment "  Update function when there is no key; 0 = success, 1 = max length exceeded")]
let blake2s_128_no_key_update : F.update_st (blake2s_128 0) =
  F.mk_update #(blake2s_128 0)
    (blake2_update_multi Spec.Blake2S M128 0 Blake2s128.blake2s_update_multi)

[@ (Comment "  Finish function when there is no key")]
let blake2s_128_no_key_finish : F.finish_st (blake2s_128 0) =
  F.mk_finish #(blake2s_128 0)
    (blake2_finish Spec.Blake2S M128 0 Blake2s128.blake2s_finish)
    (blake2_update_last Spec.Blake2S M128 0 Blake2s128.blake2s_update_last)
    (blake2_update_multi Spec.Blake2S M128 0 Blake2s128.blake2s_update_multi)
    (state_copy Spec.Blake2S M128)
    (state_alloca Spec.Blake2S M128)

[@ (Comment "  Free state function when there is no key")]
let blake2s_128_no_key_free : F.free_st (blake2s_128 0) =
  F.mk_free #(blake2s_128 0)
    (state_free Spec.Blake2S M128)
    (key_free Spec.Blake2S 0)
