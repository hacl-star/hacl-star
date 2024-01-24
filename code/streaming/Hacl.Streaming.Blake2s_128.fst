module Hacl.Streaming.Blake2s_128

module Blake2s128 = Hacl.Blake2s_128
module Common = Hacl.Streaming.Blake2.Common
module Core = Hacl.Impl.Blake2.Core
module F = Hacl.Streaming.Functor
module G = FStar.Ghost
module Impl = Hacl.Impl.Blake2.Generic
module Spec = Spec.Blake2

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

/// The functor
inline_for_extraction noextract
let blake2s_128 kk =
  Common.blake2 Spec.Blake2S Core.M128 kk Blake2s128.init_with_params Blake2s128.update_multi
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

(* The one-shot hash *)
[@@ Comment "Write the BLAKE2s digest of message `input` using key `key` into `output`.

@param output Pointer to `output_len` bytes of memory where the digest is written to.
@param output_len Length of the to-be-generated digest with 1 <= `output_len` <= 32.
@param input Pointer to `input_len` bytes of memory where the input message is read from.
@param input_len Length of the input message.
@param key Pointer to `key_len` bytes of memory where the key is read from.
@param key_len Length of the key. Can be 0."]
let hash_with_key : Impl.blake2_st Spec.Blake2S Core.M128 =
  Impl.blake2 #Spec.Blake2S #Core.M128 Blake2s128.init Blake2s128.update Blake2s128.finish
