module HaclProvider

open FStar.HyperStack.All
open FStar.Bytes

assume val crypto_scalarmult:
  secret:lbytes 32 ->
  point:lbytes 32 ->
  EXT (lbytes 32)
