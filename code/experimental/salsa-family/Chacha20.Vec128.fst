module Chacha20.Vec128


open FStar.Buffer


#reset-options "--max_fuel 0 --z3rlimit 20"


open Hacl.Impl.Chacha20.Vec128

let chacha20 output plain len k n ctr =
  let h0 = ST.get() in
  chacha20 output plain len k n ctr;
  let h1 = ST.get() in
  Spec.Chacha20_vec1.Lemmas.lemma_chacha20_encrypt_bytes (as_seq h0 k) (as_seq h0 n) (UInt32.v ctr) (as_seq h0 plain)
