module Hacl.Streaming.Blake2.Types

module Common = Hacl.Streaming.Blake2.Common
module Core = Hacl.Impl.Blake2.Core
module G = FStar.Ghost
module Spec = Spec.Blake2

let block_state_blake2b_32 (kk: G.erased (Common.index Spec.Blake2B)) =
  Common.s Spec.Blake2B kk Core.M32
let optional_block_state_blake2b_32 (kk: G.erased (Common.index Spec.Blake2B)) =
  option (block_state_blake2b_32 kk)

let block_state_blake2b_256 (kk: G.erased (Common.index Spec.Blake2B)) =
  Common.s Spec.Blake2B kk Core.M256
let optional_block_state_blake2b_256 (kk: G.erased (Common.index Spec.Blake2B)) =
  option (block_state_blake2b_256 kk)

let block_state_blake2s_32 (kk: G.erased (Common.index Spec.Blake2S)) =
  Common.s Spec.Blake2S kk Core.M32
let optional_block_state_blake2s_32 (kk: G.erased (Common.index Spec.Blake2S)) =
  option (block_state_blake2s_32 kk)

let block_state_blake2s_128 (kk: G.erased (Common.index Spec.Blake2S)) =
  Common.s Spec.Blake2S kk Core.M128
let optional_block_state_blake2s_128 (kk: G.erased (Common.index Spec.Blake2S)) =
  option (block_state_blake2s_128 kk)
