module Hacl.Streaming.Blake2b_256

module Blake2b256 = Hacl.Blake2b_256
module Common = Hacl.Streaming.Blake2.Common
module Core = Hacl.Impl.Blake2.Core
module F = Hacl.Streaming.Functor
module G = FStar.Ghost
module Spec = Spec.Blake2

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

/// The functor
inline_for_extraction noextract
let blake2b_256 kk =
  Common.blake2 Spec.Blake2B Core.M256 kk Blake2b256.init Blake2b256.update_multi
         Blake2b256.update_last Blake2b256.finish

/// Type abbreviations
let block_state_t = Common.s Spec.Blake2B Core.M256
let state_t = F.state_s (blake2b_256 0) () (Common.s Spec.Blake2B Core.M256) (Common.empty_key Spec.Blake2B)

/// No key
inline_for_extraction noextract
let alloca =
  F.alloca (blake2b_256 0) () (Common.s Spec.Blake2B Core.M256) (Common.empty_key Spec.Blake2B)

[@ (Comment "  State allocation function when there is no key")]
let malloc =
  F.malloc (blake2b_256 0) () (Common.s Spec.Blake2B Core.M256) (Common.empty_key Spec.Blake2B)

[@ (Comment "  Re-initialization function when there is no key")]
let reset =
  F.reset (blake2b_256 0) () (Common.s Spec.Blake2B Core.M256) (Common.empty_key Spec.Blake2B)

[@ (Comment "  Update function when there is no key; 0 = success, 1 = max length exceeded")]
let update =
  F.update (blake2b_256 0) (G.hide ()) (Common.s Spec.Blake2B Core.M256) (Common.empty_key Spec.Blake2B)

[@ (Comment "  Finish function when there is no key")]
let digest =
  F.digest (blake2b_256 0) () (Common.s Spec.Blake2B Core.M256) (Common.empty_key Spec.Blake2B)

[@ (Comment "  Free state function when there is no key")]
let free =
  F.free (blake2b_256 0) (G.hide ()) (Common.s Spec.Blake2B Core.M256) (Common.empty_key Spec.Blake2B)
