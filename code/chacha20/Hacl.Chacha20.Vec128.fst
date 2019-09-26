module Hacl.Chacha20.Vec128

open Hacl.Meta.Chacha20.Vec

private
let double_round_128 = double_round_inline #4
private
let chacha20_core_128 = chacha20_core_inline #4 double_round_128
private
let chacha20_init_128 = chacha20_init_inline #4

let chacha20_encrypt_128 = chacha20_encrypt_inline #4 chacha20_init_128 chacha20_core_128
let chacha20_decrypt_128 = chacha20_decrypt_inline #4 chacha20_init_128 chacha20_core_128
