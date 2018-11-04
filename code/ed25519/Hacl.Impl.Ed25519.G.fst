module Hacl.Impl.Ed25519.G

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Buffer

open Hacl.Bignum25519
open Hacl.Impl.Ed25519.ExtPoint

#reset-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
val make_g:
  g:point ->
  Stack unit
    (requires (fun h -> live h g))
    (ensures (fun h0 _ h1 -> live h1 g /\ modifies_1 g h0 h1 /\ as_point h1 g == Spec.Ed25519.g
      /\ point_inv h1 g))

#reset-options "--max_fuel 0 --z3rlimit 200"

let make_g g =
  assert_norm (pow2 51 = 0x8000000000000);
  assert_norm((0x00062d608f25d51a + pow2 51 * 0x000412a4b4f6592a + pow2 102 * 0x00075b7171a4b31d + pow2 153 * 0x0001ff60527118fe + pow2 204 * 0x000216936d3cd6e5) % (pow2 255 - 19) = Mktuple4?._1 Spec.Ed25519.g);
  assert_norm((0x0006666666666658 + pow2 51 *  0x0004cccccccccccc + pow2 102 *  0x0001999999999999 + pow2 153 *  0x0003333333333333 + pow2 204 * 0x0006666666666666) % (pow2 255 - 19) = Mktuple4?._2 Spec.Ed25519.g);
  assert_norm((1 + pow2 51 * 0 + pow2 102 * 0 + pow2 153 * 0 + pow2 204 * 0) % (pow2 255 - 19) = Mktuple4?._3 Spec.Ed25519.g);
  assert_norm((0x00068ab3a5b7dda3 + pow2 51 * 0x00000eea2a5eadbb + pow2 102 * 0x0002af8df483c27e + pow2 153 * 0x000332b375274732 + pow2 204 * 0x00067875f0fd78b7) % (pow2 255 - 19) = Mktuple4?._4 Spec.Ed25519.g);
  let gx = Hacl.Impl.Ed25519.ExtPoint.getx g in
  let gy = Hacl.Impl.Ed25519.ExtPoint.gety g in
  let gz = Hacl.Impl.Ed25519.ExtPoint.getz g in
  let gt = Hacl.Impl.Ed25519.ExtPoint.gett g in
  let h0 = ST.get() in
  Hacl.Lib.Create64.make_h64_5 gx (Hacl.Cast.uint64_to_sint64 0x00062d608f25d51auL) (Hacl.Cast.uint64_to_sint64 0x000412a4b4f6592auL) (Hacl.Cast.uint64_to_sint64 0x00075b7171a4b31duL) (Hacl.Cast.uint64_to_sint64 0x0001ff60527118feuL) (Hacl.Cast.uint64_to_sint64 0x000216936d3cd6e5uL);
  let h1 = ST.get() in
  lemma_intro_red_51 (as_seq h1 gx);
  lemma_red_51_is_red_513 (as_seq h1 gx);
  lemma_reveal_seval (as_seq h1 gx);
  Hacl.Lib.Create64.make_h64_5 gy (Hacl.Cast.uint64_to_sint64 0x0006666666666658uL) (Hacl.Cast.uint64_to_sint64 0x0004ccccccccccccuL) (Hacl.Cast.uint64_to_sint64 0x0001999999999999uL) (Hacl.Cast.uint64_to_sint64 0x0003333333333333uL) (Hacl.Cast.uint64_to_sint64 0x0006666666666666uL);
  let h2 = ST.get() in
  lemma_intro_red_51 (as_seq h2 gy);
  lemma_red_51_is_red_513 (as_seq h2 gy);
  lemma_reveal_seval (as_seq h2 gy);
  no_upd_lemma_1 h1 h2 gy gx;
  Hacl.Lib.Create64.make_h64_5 gz (Hacl.Cast.uint64_to_sint64 0x0000000000000001uL) (Hacl.Cast.uint64_to_sint64 0x0000000000000000uL) (Hacl.Cast.uint64_to_sint64 0x0000000000000000uL) (Hacl.Cast.uint64_to_sint64 0x0000000000000000uL) (Hacl.Cast.uint64_to_sint64 0x0000000000000000uL);
  let h3 = ST.get() in
  lemma_intro_red_51 (as_seq h3 gz);
  lemma_red_51_is_red_513 (as_seq h3 gz);
  lemma_reveal_seval (as_seq h3 gz);
  no_upd_lemma_1 h2 h3 gz gx;
  no_upd_lemma_1 h2 h3 gz gy;
  Hacl.Lib.Create64.make_h64_5 gt (Hacl.Cast.uint64_to_sint64 0x00068ab3a5b7dda3uL) (Hacl.Cast.uint64_to_sint64 0x00000eea2a5eadbbuL) (Hacl.Cast.uint64_to_sint64 0x0002af8df483c27euL) (Hacl.Cast.uint64_to_sint64 0x000332b375274732uL) (Hacl.Cast.uint64_to_sint64 0x00067875f0fd78b7uL);
  let h4 = ST.get() in
  lemma_intro_red_51 (as_seq h4 gt);
  lemma_red_51_is_red_513 (as_seq h4 gt);
  lemma_reveal_seval (as_seq h4 gt);
  no_upd_lemma_1 h3 h4 gt gx;
  no_upd_lemma_1 h3 h4 gt gy;
  no_upd_lemma_1 h3 h4 gt gz
