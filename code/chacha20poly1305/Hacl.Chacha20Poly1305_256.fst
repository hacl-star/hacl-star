module Hacl.Chacha20Poly1305_256

open Hacl.Meta.Chacha20Poly1305
open Hacl.Impl.Chacha20Poly1305
open Hacl.Impl.Poly1305.Fields

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

private
let poly1305_padded_256 = poly1305_padded_higher #M256
private
let poly1305_do_256 = poly1305_do_higher #M256 poly1305_padded_256

let aead_encrypt : aead_encrypt_st M256 =
  aead_encrypt_higher #M256 poly1305_do_256 Hacl.Chacha20.Vec256.chacha20_encrypt_256

let aead_decrypt : aead_decrypt_st M256 =
  aead_decrypt_higher #M256 Hacl.Chacha20.Vec256.chacha20_encrypt_256 poly1305_do_256
