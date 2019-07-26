module Hacl.Chacha20.Vec256

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Chacha20.Vec

let chacha20_encrypt : chacha20_encrypt_st 8 =
  chacha20_encrypt

let chacha20_decrypt : chacha20_decrypt_st 8 =
  chacha20_decrypt
