module Hacl.Chacha20Poly1305_256

open Hacl.Impl.Chacha20Poly1305
open Hacl.Impl.Poly1305.Fields

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let aead_encrypt : aead_encrypt_st M256 =
  aead_encrypt

let aead_decrypt : aead_decrypt_st M256 =
  aead_decrypt
