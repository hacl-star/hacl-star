module Spec.Poly1305.Lemmas

open FStar.Mul
open FStar.Seq
open FStar.UInt8
open FStar.Endianness


val lemma_prime_value: n:nat -> Lemma
  (requires (n = 130))
  (ensures (pow2 n - 5 = 0x3fffffffffffffffffffffffffffffffb))
  [SMTPat (pow2 n - 5)]
let lemma_prime_value n = assert_norm(pow2 130 - 5 = 0x3fffffffffffffffffffffffffffffffb)

val lemma_encode_bound: w:seq t{length w < 16} -> Lemma
  (requires (True))
  (ensures (little_endian w < 0x3fffffffffffffffffffffffffffffffb
    /\ pow2 (8 * length w) < 0x3fffffffffffffffffffffffffffffffb))
  [SMTPat (pow2 (8 * length w))]
let lemma_encode_bound w =
  let l = length w in
  Math.Lemmas.pow2_le_compat 128 (8 * l);
  assert_norm(pow2 128 < pow2 130 - 5);
  lemma_little_endian_is_bounded w

val lemma_encode_r: r:seq t{length r = 16} -> Lemma
  (requires (True))
  (ensures (little_endian r < pow2 128 /\ pow2 128 = 0x100000000000000000000000000000000))
  [SMTPat (UInt.logand #128 (little_endian r) 0x0ffffffc0ffffffc0ffffffc0fffffff)]
let lemma_encode_r r =
  lemma_little_endian_is_bounded r;
  assert_norm(pow2 128 = 0x100000000000000000000000000000000)

let append_last = snoc
