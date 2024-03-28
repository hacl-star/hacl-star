module Hacl.Streaming.Blake2b_256

module Blake2b256 = Hacl.Blake2b_256
module Common = Hacl.Streaming.Blake2.Common
module Core = Hacl.Impl.Blake2.Core
module F = Hacl.Streaming.Functor
module G = FStar.Ghost
module Impl = Hacl.Impl.Blake2.Generic
module Spec = Spec.Blake2

inline_for_extraction noextract
let blake2b_256 =
  Common.blake2 Spec.Blake2B Core.M256 Blake2b256.init Blake2b256.update_multi
         Blake2b256.update_last Blake2b256.finish

/// Type abbreviations - makes Karamel use pretty names in the generated code

let block_state_t (kk: G.erased (Common.key_size_t Spec.Blake2B)) = Common.s Spec.Blake2B kk Core.M256
let state_t (kk: G.erased (Common.key_size_t Spec.Blake2B)) =
  F.state_s blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

/// The incremental hash functions instantiations. Note that we can't write a
/// generic one, because the normalization then performed by KaRaMeL explodes.

/// All those implementations are for non-keyed hash.

inline_for_extraction noextract
[@ (Comment "  State allocation function when there is no key")]
let alloca_raw (kk: Common.key_size_t Spec.Blake2B): Tot _ =
  F.alloca blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

[@ (Comment "  State allocation function when there is no key")]
let malloc_raw (kk: Common.key_size_t Spec.Blake2B): Tot _ =
  F.malloc blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

[@ (Comment "  Re-initialization function when there is no key")]
let reset (kk: G.erased (Common.key_size_t Spec.Blake2B)): Tot _ =
  F.reset blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

[@ (Comment "  Update function when there is no key; 0 = success, 1 = max length exceeded")]
let update (kk: G.erased (Common.key_size_t Spec.Blake2B)): Tot _ =
  F.update blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

[@ (Comment "  Finish function when there is no key")]
let digest_raw (kk: Common.key_size_t Spec.Blake2B): Tot _ =
  F.digest blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

[@ (Comment "  Free state function when there is no key")]
let free (kk: G.erased (Common.key_size_t Spec.Blake2B)): Tot _ =
  F.free blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

let copy (kk: G.erased (Common.key_size_t Spec.Blake2B)): Tot _ =
  F.copy blake2b_256 kk (Common.s Spec.Blake2B kk Core.M256) (Common.blake_key Spec.Blake2B kk)

(* The one-shot hash *)
[@@ Comment "Write the BLAKE2b digest of message `input` using key `key` into `output`.

@param output Pointer to `output_len` bytes of memory where the digest is written to.
@param output_len Length of the to-be-generated digest with 1 <= `output_len` <= 64.
@param input Pointer to `input_len` bytes of memory where the input message is read from.
@param input_len Length of the input message.
@param key Pointer to `key_len` bytes of memory where the key is read from.
@param key_len Length of the key. Can be 0."]
let hash_with_key : Impl.blake2_st Spec.Blake2B Core.M256 =
  Impl.blake2 #Spec.Blake2B #Core.M256 Blake2b256.init Blake2b256.update Blake2b256.finish
