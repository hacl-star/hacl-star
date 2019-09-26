module Hacl.Chacha20.Vec32

open Hacl.Meta.Chacha20.Vec

private
let double_round_32 = double_round_inline #1
private
let chacha20_core_32 = chacha20_core_inline #1 double_round_32
private
let chacha20_init_32 = chacha20_init_inline #1

let chacha20_encrypt_32 = chacha20_encrypt_inline #1 chacha20_init_32 chacha20_core_32
let chacha20_decrypt_32 = chacha20_decrypt_inline #1 chacha20_init_32 chacha20_core_32
