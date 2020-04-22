module Hacl.Chacha20.Vec256

open Hacl.Meta.Chacha20.Vec

[@CInline]
private
let double_round_256 = Hacl.Impl.Chacha20.Core32xN.double_round #8
[@CInline]
private
let chacha20_core_256 = vec_chacha20_core_higher #8 True double_round_256
[@CInline]
private
let chacha20_init_256 = Hacl.Impl.Chacha20.Vec.chacha20_init #8

let chacha20_encrypt_256 = vec_chacha20_encrypt_higher #8 True chacha20_init_256 chacha20_core_256
let chacha20_decrypt_256 = vec_chacha20_decrypt_higher #8 True chacha20_init_256 chacha20_core_256
