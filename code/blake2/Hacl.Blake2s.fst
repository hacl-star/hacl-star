module Hacl.Blake2s

module Spec = Spec.Blake2
module Impl = Hacl.Impl.Blake2


private
let blake2s_compress = Impl.blake2_compress Spec.Blake2S

let blake2s_update_block = Impl.blake2_update_block Spec.Blake2S blake2s_compress

let blake2s_init = Impl.blake2_init Spec.Blake2S blake2s_update_block

let blake2s_update_block_multi = Impl.blake2_update_block_multi Spec.Blake2S blake2s_update_block

let blake2s_update_last = Impl.blake2_update_last Spec.Blake2S blake2s_update_block

let blake2s_finish = Impl.blake2_finish Spec.Blake2S

let blake2s = Impl.blake2 Spec.Blake2S blake2s_init blake2s_update_block_multi blake2s_update_last blake2s_finish
