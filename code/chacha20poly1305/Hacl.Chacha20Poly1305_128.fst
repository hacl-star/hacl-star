module Hacl.Chacha20Poly1305_128


open Hacl.Meta.Chacha20Poly1305
open Hacl.Impl.Chacha20Poly1305
open Hacl.Impl.Poly1305.Fields
open Hacl.Poly1305_128

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

[@CInline]
private
let poly1305_padded_128 = Hacl.Impl.Chacha20Poly1305.PolyCore.poly1305_padded #M128
[@CInline]
private
let poly1305_do_128 = chacha20poly1305_poly1305_do_higher #M128 True poly1305_finish poly1305_init poly1305_padded_128

let aead_encrypt : aead_encrypt_st M128 =
  chacha20poly1305_aead_encrypt_higher #M128 True poly1305_do_128 Hacl.Chacha20.Vec128.chacha20_encrypt_128

let aead_decrypt : aead_decrypt_st M128 =
  chacha20poly1305_aead_decrypt_higher #M128 True Hacl.Chacha20.Vec128.chacha20_encrypt_128 poly1305_do_128
