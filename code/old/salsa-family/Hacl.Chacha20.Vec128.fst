module Hacl.Chacha20.Vec128

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Buffer


#reset-options "--max_fuel 0 --z3rlimit 20"


open Hacl.Impl.Chacha20.Vec128
open Hacl.Spec.Endianness

let chacha20 output plain len k n ctr =
  let h0 = ST.get() in
  chacha20 output plain len k n ctr;
  let h1 = ST.get() in
  Spec.Chacha20_vec1.Lemmas.lemma_chacha20_encrypt_bytes (reveal_sbytes (as_seq h0 k)) (reveal_sbytes (as_seq h0 n)) (UInt32.v ctr) (reveal_sbytes (as_seq h0 plain))
