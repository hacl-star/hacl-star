module Hacl.Streaming.Blake2b_32

module Blake2b32 = Hacl.Blake2b_32
module Common = Hacl.Streaming.Blake2.Common
module Core = Hacl.Impl.Blake2.Core
module F = Hacl.Streaming.Functor
module G = FStar.Ghost
module Spec = Spec.Blake2

inline_for_extraction noextract
let blake2b_32 kk =
  Common.blake2 Spec.Blake2B Core.M32 kk Blake2b32.blake2b_init Blake2b32.blake2b_update_multi
         Blake2b32.blake2b_update_last Blake2b32.blake2b_finish

/// Type abbreviations - makes Karamel use pretty names in the generated code

let block_state = Common.s Spec.Blake2B Core.M32
let state = F.state_s (blake2b_32 0) () (Common.s Spec.Blake2B Core.M32) (Common.empty_key Spec.Blake2B)

/// The incremental hash functions instantiations. Note that we can't write a
/// generic one, because the normalization then performed by KaRaMeL explodes.

/// All those implementations are for non-keyed hash.

inline_for_extraction noextract
[@ (Comment "  State allocation function when there is no key")]
let alloca =
  F.alloca (blake2b_32 0) () (Common.s Spec.Blake2B Core.M32) (Common.empty_key Spec.Blake2B)

[@ (Comment "  State allocation function when there is no key")]
let malloc =
  F.malloc (blake2b_32 0) () (Common.s Spec.Blake2B Core.M32) (Common.empty_key Spec.Blake2S)

[@ (Comment "  Re-initialization function when there is no key")]
let reset =
  F.reset (blake2b_32 0) () (Common.s Spec.Blake2B Core.M32) (Common.empty_key Spec.Blake2S)

[@ (Comment "  Update function when there is no key; 0 = success, 1 = max length exceeded")]
let update =
  F.update (blake2b_32 0) (G.hide ()) (Common.s Spec.Blake2B Core.M32) (Common.empty_key Spec.Blake2S)

[@ (Comment "  Finish function when there is no key")]
let digest =
  F.digest (blake2b_32 0) () (Common.s Spec.Blake2B Core.M32) (Common.empty_key Spec.Blake2S)

[@ (Comment "  Free state function when there is no key")]
let free =
  F.free (blake2b_32 0) (G.hide ()) (Common.s Spec.Blake2B Core.M32) (Common.empty_key Spec.Blake2S)
