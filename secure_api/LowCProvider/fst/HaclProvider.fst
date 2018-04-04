module HaclProvider

open FStar.HyperStack.All
open FStar.Bytes

assume val crypto_scalarmult:
  secret: lbytes 32 ->
  point: lbytes 32 ->
  EXT (lbytes 32)

type hash_alg =
  | HACL_SHA256
  | HACL_SHA384
  | HACL_SHA512

let hash_size = function
  | HACL_SHA256 -> 32
  | HACL_SHA384 -> 48
  | HACL_SHA512 -> 64

assume val crypto_hash:
  alg: hash_alg ->
  msg: bytes ->
  EXT (lbytes (hash_size alg))

assume val crypto_hmac:
  alg: hash_alg ->
  key: bytes ->
  msg: bytes ->
  EXT (lbytes (hash_size alg))
