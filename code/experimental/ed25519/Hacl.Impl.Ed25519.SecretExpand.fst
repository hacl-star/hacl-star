module Hacl.Impl.Ed25519.SecretExpand

open FStar.Buffer
open Hacl.UInt8


#reset-options "--max_fuel 0 --z3rlimit 20"
let secret_expand expanded secret =
  let h0 = ST.get() in
  Hacl.Impl.Sha512.sha512 expanded secret 32ul;
  let h = ST.get() in
  assert_norm(pow2 125 > 32);
  let h_low  = Buffer.sub expanded 0ul  32ul in
  let h_high = Buffer.sub expanded 32ul 32ul in
  assert((as_seq h h_low, as_seq h h_high) == Seq.split (as_seq h expanded) 32);
  let h_low0  = h_low.( 0ul) in
  let h_low31 = h_low.(31ul) in
  h_low.( 0ul) <- (h_low0 &^ 0xf8uy);
  h_low.(31ul) <- ((h_low31 &^ 127uy) |^ 64uy);
  let h' = ST.get() in
  no_upd_lemma_1 h h' h_low h_high;
  assert( as_seq h' h_high == as_seq h h_high);
  Seq.lemma_eq_intro (Seq.append (as_seq h h_low) (as_seq h (Buffer.sub expanded 32ul 32ul))) (as_seq h expanded)
