module Hacl.Streaming.Blake2.Types.Simd128

module Common = Hacl.Streaming.Blake2.Common
module Core = Hacl.Impl.Blake2.Core
module G = FStar.Ghost
module Spec = Spec.Blake2

private
let two_vec128 = Core.(state_p Spec.Blake2S M128 & state_p Spec.Blake2S M128)

[@ CAbstractStruct ]
let block_state_blake2s_128 (kk: G.erased (Common.index Spec.Blake2S)) =
  // Make sure two_vec128 is actually used!
  let open Common in
  let open Hacl.Streaming.Blake2.Params in
  singleton (kk.key_length) & singleton (kk.digest_length) & singleton_b (kk.last_node) & two_vec128
