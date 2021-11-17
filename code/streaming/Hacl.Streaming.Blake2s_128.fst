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
let blake2s_128 =
  blake2 Spec.Blake2S M128 Blake2s128.blake2s_init Blake2s128.blake2s_update_multi
         Blake2s128.blake2s_update_last Blake2s128.blake2s_finish

/// Type abbreviations
let blake2s_128_block_state = s Spec.Blake2S M128
let blake2s_128_state = F.state_s blake2s_128 () (s Spec.Blake2S M128) unit_key

/// No key
inline_for_extraction noextract
let blake2s_128_no_key_alloca =
  F.alloca blake2s_128 () (s Spec.Blake2S M128) unit_key

[@ (Comment "  State allocation function when there is no key")]
let blake2s_128_no_key_create_in =
  F.create_in blake2s_128 () (s Spec.Blake2S M128) unit_key

[@ (Comment "  (Re-)initialization function when there is no key")]
let blake2s_128_no_key_init =
  F.init blake2s_128 () (s Spec.Blake2S M128) unit_key

[@ (Comment "  Update function when there is no key")]
let blake2s_128_no_key_update =
  F.update blake2s_128 (G.hide ()) (s Spec.Blake2S M128) unit_key

[@ (Comment "  Finish function when there is no key")]
let blake2s_128_no_key_finish =
  F.mk_finish blake2s_128 () (s Spec.Blake2S M128) unit_key

[@ (Comment "  Free state function when there is no key")]
let blake2s_128_no_key_free =
  F.free blake2s_128 (G.hide ()) (s Spec.Blake2S M128) unit_key
