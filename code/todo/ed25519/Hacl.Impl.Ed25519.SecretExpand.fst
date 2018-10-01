module Hacl.Impl.Ed25519.SecretExpand

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open Hacl.UInt8


#reset-options "--max_fuel 0 --z3rlimit 200"

let secret_expand expanded secret =
  assert_norm(pow2 32 = 0x100000000);
  assert_norm(pow2 125 = 0x20000000000000000000000000000000);
  let h0 = ST.get() in
  Hacl.SHA2_512.hash expanded secret 32ul;
  let h = ST.get() in
  assert_norm(pow2 125 > 32);
  let h_low  = Buffer.sub expanded 0ul  32ul in
  let h_high = Buffer.sub expanded 32ul 32ul in
  assert((as_seq h h_low, as_seq h h_high) == Seq.split (as_seq h expanded) 32);
  let h_low0  = h_low.( 0ul) in
  let h_low31 = h_low.(31ul) in
  h_low.( 0ul) <- (h_low0 &^ Hacl.Cast.uint8_to_sint8 0xf8uy);
  h_low.(31ul) <- ((h_low31 &^ Hacl.Cast.uint8_to_sint8 127uy) |^ Hacl.Cast.uint8_to_sint8 64uy);
  let h' = ST.get() in
  no_upd_lemma_1 h h' h_low h_high;
  assert( as_seq h' h_high == as_seq h h_high);
  Seq.lemma_eq_intro (Seq.append (as_seq h h_low) (as_seq h (Buffer.sub expanded 32ul 32ul))) (as_seq h expanded)
