module Hacl.Streaming.Blake2b_256

module G = FStar.Ghost
module F = Hacl.Streaming.Functor

module Spec = Spec.Blake2
open Hacl.Impl.Blake2.Core
open Hacl.Streaming.Blake2
module Blake2b256 = Hacl.Blake2b_256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

/// The functor
inline_for_extraction noextract
let blake2b_256 kk = blake2_index Spec.Blake2B M256 kk

/// Type abbreviations
let blake2b_256_block_state = s Spec.Blake2B M256
let blake2b_256_state = F.state_s (blake2b_256 0) (s Spec.Blake2B M256) (empty_key Spec.Blake2B)

/// No key
inline_for_extraction noextract
let blake2b_256_no_key_alloca : F.alloca_st (blake2b_256 0) =
  F.mk_alloca #(blake2b_256 0)
    (blake2_init Spec.Blake2B M256 0 Blake2b256.blake2b_init)
    (key_copy Spec.Blake2B 0)
    (key_alloca Spec.Blake2B 0)
    (state_alloca Spec.Blake2B M256)

[@ (Comment "  Copy function when there is no key")]
let blake2b_256_no_key_copy : F.copy_st (blake2b_256 0) =
  F.mk_copy #(blake2b_256 0)
    (key_copy Spec.Blake2B 0)
    (key_create_in Spec.Blake2B 0)
    (state_copy Spec.Blake2B M256)
    (state_create_in Spec.Blake2B M256)

[@ (Comment "  State allocation function when there is no key")]
let blake2b_256_no_key_create_in : F.create_in_st (blake2b_256 0) =
  F.mk_create_in #(blake2b_256 0)
    (blake2_init Spec.Blake2B M256 0 Blake2b256.blake2b_init)
    (key_copy Spec.Blake2B 0)
    (key_create_in Spec.Blake2B 0)
    (state_create_in Spec.Blake2B M256)

[@ (Comment "  (Re-)initialization function when there is no key")]
let blake2b_256_no_key_init : F.init_st (blake2b_256 0) =
  F.mk_init #(blake2b_256 0)
    (key_copy Spec.Blake2B 0)
    (blake2_init Spec.Blake2B M256 0 Blake2b256.blake2b_init)

[@ (Comment "  Update function when there is no key; 0 = success, 1 = max length exceeded")]
let blake2b_256_no_key_update : F.update_st (blake2b_256 0) =
  F.mk_update #(blake2b_256 0)
    (blake2_update_multi Spec.Blake2B M256 0 Blake2b256.blake2b_update_multi)

[@ (Comment "  Finish function when there is no key")]
let blake2b_256_no_key_finish : F.finish_st (blake2b_256 0) =
  F.mk_finish #(blake2b_256 0)
    (blake2_finish Spec.Blake2B M256 0 Blake2b256.blake2b_finish)
    (blake2_update_last Spec.Blake2B M256 0 Blake2b256.blake2b_update_last)
    (blake2_update_multi Spec.Blake2B M256 0 Blake2b256.blake2b_update_multi)
    (state_copy Spec.Blake2B M256)
    (state_alloca Spec.Blake2B M256)

[@ (Comment "  Free state function when there is no key")]
let blake2b_256_no_key_free : F.free_st (blake2b_256 0) =
  F.mk_free #(blake2b_256 0)
    (state_free Spec.Blake2B M256)
    (key_free Spec.Blake2B 0)
