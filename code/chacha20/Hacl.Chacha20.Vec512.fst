module Hacl.Chacha20.Vec512

open Hacl.Meta.Chacha20.Vec

[@CInline]
private
let double_round_512 = Hacl.Impl.Chacha20.Core32xN.double_round #16
[@CInline]
private
let chacha20_core_512 = vec_chacha20_core_higher #16 True double_round_512
[@CInline]
private
let chacha20_init_512 = Hacl.Impl.Chacha20.Vec.chacha20_init #16

let chacha20_encrypt_512 = vec_chacha20_encrypt_higher #16 True chacha20_init_512 chacha20_core_512
let chacha20_decrypt_512 = vec_chacha20_decrypt_higher #16 True chacha20_init_512 chacha20_core_512
