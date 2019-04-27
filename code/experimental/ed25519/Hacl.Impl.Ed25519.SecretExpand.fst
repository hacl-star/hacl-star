module Hacl.Impl.Ed25519.SecretExpand

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

val secret_expand:
    expanded:lbuffer uint8 64ul
  -> secret:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h expanded /\ live h secret /\ disjoint secret expanded)
    (ensures  fun h0 _ h1 -> modifies (loc expanded) h0 h1)
let secret_expand expanded secret =
  Hacl.Hash.SHA2.hash_512_lib 32ul secret expanded;
  let h_low  = sub expanded 0ul  32ul in
  let h_high = sub expanded 32ul 32ul in
  let h_low0  = h_low.( 0ul) in
  let h_low31 = h_low.(31ul) in
  h_low.( 0ul) <- h_low0 &. u8 0xf8;
  h_low.(31ul) <- (h_low31 &. u8 127) |. u8 64
