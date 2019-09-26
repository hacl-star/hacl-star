module Hacl.Chacha20.Vec256

open Hacl.Meta.Chacha20.Vec

private
let double_round_256 = double_round_inline #8
private
let chacha20_core_256 = chacha20_core_inline #8 double_round_256
private
let chacha20_init_256 = chacha20_init_inline #8

let chacha20_encrypt_256 = chacha20_encrypt_inline #8 chacha20_init_256 chacha20_core_256
let chacha20_decrypt_256 = chacha20_decrypt_inline #8 chacha20_init_256 chacha20_core_256
