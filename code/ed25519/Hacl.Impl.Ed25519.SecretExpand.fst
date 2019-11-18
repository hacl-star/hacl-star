module Hacl.Impl.Ed25519.SecretExpand

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

#set-options "--z3rlimit 10 --max_fuel 0 --max_ifuel 0"

let secret_expand expanded secret =
  assert_norm(pow2 32 <= pow2 125 - 1);
  Hacl.Hash.SHA2.hash_512_lib 32ul secret expanded;
  let h_low  = sub expanded 0ul  32ul in
  let h_high = sub expanded 32ul 32ul in
  let h_low0  = h_low.( 0ul) in
  let h_low31 = h_low.(31ul) in
  h_low.( 0ul) <- h_low0 &. u8 0xf8;
  h_low.(31ul) <- (h_low31 &. u8 127) |. u8 64
