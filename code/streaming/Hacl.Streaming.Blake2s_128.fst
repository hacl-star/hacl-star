module Hacl.Streaming.Blake2s_128

module Blake2s128 = Hacl.Blake2s_128
module Common = Hacl.Streaming.Blake2.Common
module Core = Hacl.Impl.Blake2.Core
module F = Hacl.Streaming.Functor
module G = FStar.Ghost
module Spec = Spec.Blake2

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

/// The functor
inline_for_extraction noextract
let blake2s_128 kk =
  Common.blake2 Spec.Blake2S Core.M128 kk Blake2s128.init Blake2s128.update_multi
         Blake2s128.update_last Blake2s128.finish

/// Type abbreviations
let block_state_t = Common.s Spec.Blake2S Core.M128
let state_t = F.state_s (blake2s_128 0) () (Common.s Spec.Blake2S Core.M128) (Common.empty_key Spec.Blake2S)

/// No key
inline_for_extraction noextract
let alloca =
  F.alloca (blake2s_128 0) () (Common.s Spec.Blake2S Core.M128) (Common.empty_key Spec.Blake2S)

[@ (Comment "  State allocation function when there is no key")]
let malloc =
  F.malloc (blake2s_128 0) () (Common.s Spec.Blake2S Core.M128) (Common.empty_key Spec.Blake2S)

[@ (Comment "  Re-initialization function when there is no key")]
let reset =
  F.reset (blake2s_128 0) () (Common.s Spec.Blake2S Core.M128) (Common.empty_key Spec.Blake2S)

[@ (Comment "  Update function when there is no key; 0 = success, 1 = max length exceeded")]
let update =
  F.update (blake2s_128 0) (G.hide ()) (Common.s Spec.Blake2S Core.M128) (Common.empty_key Spec.Blake2S)

[@ (Comment "  Finish function when there is no key")]
let digest =
  F.digest (blake2s_128 0) () (Common.s Spec.Blake2S Core.M128) (Common.empty_key Spec.Blake2S)

[@ (Comment "  Free state function when there is no key")]
let free =
  F.free (blake2s_128 0) (G.hide ()) (Common.s Spec.Blake2S Core.M128) (Common.empty_key Spec.Blake2S)
