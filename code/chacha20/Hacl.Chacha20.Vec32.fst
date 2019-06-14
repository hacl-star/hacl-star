module Hacl.Chacha20.Vec32

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Chacha20.Vec

let chacha20_encrypt : chacha20_encrypt_st 1 =
  chacha20_encrypt

let chacha20_decrypt : chacha20_decrypt_st 1 =
  chacha20_decrypt
