module Hacl.Impl.Ed25519.SecretExpand

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

val secret_expand:
    expanded:lbuffer uint8 64ul
  -> secret:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h expanded /\ live h secret /\ disjoint expanded secret)
    (ensures  fun h0 _ h1 -> modifies (loc expanded) h0 h1 /\
      (let a, prefix = Spec.Ed25519.secret_expand (as_seq h0 secret) in
       as_seq h1 (gsub expanded 0ul 32ul) == a /\
       as_seq h1 (gsub expanded 32ul 32ul) == prefix))
