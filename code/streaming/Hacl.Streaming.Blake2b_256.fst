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
let blake2b_256 kk =
  blake2 Spec.Blake2B M256 kk Blake2b256.blake2b_init Blake2b256.blake2b_update_multi
         Blake2b256.blake2b_update_last Blake2b256.blake2b_finish

/// Type abbreviations
let blake2b_256_block_state = s Spec.Blake2B M256
let blake2b_256_state = F.state_s (blake2b_256 0) () (s Spec.Blake2B M256) (empty_key Spec.Blake2B)

/// No key
inline_for_extraction noextract
let blake2b_256_no_key_alloca =
  F.alloca (blake2b_256 0) () (s Spec.Blake2B M256) (empty_key Spec.Blake2B)

[@ (Comment "  State allocation function when there is no key")]
let blake2b_256_no_key_create_in =
  F.create_in (blake2b_256 0) () (s Spec.Blake2B M256) (empty_key Spec.Blake2B)

[@ (Comment "  (Re-)initialization function when there is no key")]
let blake2b_256_no_key_init =
  F.init (blake2b_256 0) () (s Spec.Blake2B M256) (empty_key Spec.Blake2B)

[@ (Comment "  Update function when there is no key; 0 = success, 1 = max length exceeded")]
let blake2b_256_no_key_update =
  F.update (blake2b_256 0) (G.hide ()) (s Spec.Blake2B M256) (empty_key Spec.Blake2B)

[@ (Comment "  Finish function when there is no key")]
let blake2b_256_no_key_finish =
  F.mk_finish (blake2b_256 0) () (s Spec.Blake2B M256) (empty_key Spec.Blake2B)

[@ (Comment "  Free state function when there is no key")]
let blake2b_256_no_key_free =
  F.free (blake2b_256 0) (G.hide ()) (s Spec.Blake2B M256) (empty_key Spec.Blake2B)
