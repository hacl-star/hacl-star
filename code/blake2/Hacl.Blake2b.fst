module Hacl.Blake2b

module Spec = Spec.Blake2
module Impl = Hacl.Impl.Blake2


private
let blake2b_compress = Impl.blake2_compress Spec.Blake2B

let blake2b_update_block = Impl.blake2_update_block Spec.Blake2B blake2b_compress

let blake2b_init = Impl.blake2_init Spec.Blake2B blake2b_update_block

let blake2b_update_block_multi = Impl.blake2_update_block_multi Spec.Blake2B blake2b_update_block

let blake2b_update_last = Impl.blake2_update_last Spec.Blake2B blake2b_update_block

let blake2b_finish = Impl.blake2_finish Spec.Blake2B

let blake2b = Impl.blake2 Spec.Blake2B blake2b_init blake2b_update_block_multi blake2b_update_last blake2b_finish
