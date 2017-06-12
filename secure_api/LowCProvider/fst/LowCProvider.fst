module LowCProvider

open Platform.Bytes
open CoreCrypto

assume type aead_state: Type0
assume val alg: aead_state -> GTot aead_cipher
type aes_impl =
  | HaclAES
  | ValeAES

assume val aead_create:
  a: aead_cipher ->
  aes_impl ->
  k: lbytes (aeadKeySize a) -> 
  EXT (st:aead_state{alg st = a})

assume val aead_encrypt:
  st: aead_state ->
  iv:lbytes (aeadRealIVSize (alg st)) ->
  ad:bytes ->
  plain:bytes ->
  EXT (c:bytes)

assume val aead_decrypt:
  st: aead_state ->
  iv:lbytes (aeadRealIVSize (alg st)) ->
  ad:bytes ->
  cipher:bytes{length cipher >= aeadTagSize (alg st)} ->
  EXT (o:option bytes)

