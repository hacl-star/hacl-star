module Hacl.Impl.P256.ECDSA.KeyGen


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence


val ecdsa_p256_keyGen_privateKey: random: lbuffer uint8 (size 32)
  -> privateKey: lbuffer uint8 (size 32) -> 
  Stack bool 
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)


let ecdsa_p256_keyGen_privateKey random result = true



val ecdsa_p256_keyGen_publicKey_inner: privateKey: lbuffer uint8 (size 32) 
  -> publibKey: lbuffer uint8 (size 64) -> 
  Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)


let ecdsa_p256_keyGen_publicKey_inner privateKey publicKey = ()


val ecdsa_p256_keyGen_publicKey: privateKey: lbuffer uint8 (size 32) 
  -> publicKey: lbuffer uint8 (size 64) ->
  Stack bool
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)


let ecdsa_p256_keyGen_publicKey privateKey publicKey = true
