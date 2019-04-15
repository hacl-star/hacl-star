module Spec.Curve25519.Lemmas

val lemma_prime_value: n:nat -> Lemma
  (requires (n = 255))
  (ensures (pow2 n - 19 = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed))
  [SMTPat (pow2 n - 19)]
let lemma_prime_value n = assert_norm(pow2 255 - 19 = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed)

val lemma_div_n: n:nat -> Lemma
  (requires (n > 1))
  (ensures (n / 2 < n /\ n / 2 > 0))
  [SMTPat (n / 2)]
let lemma_div_n n = ()

val lemma_pow2_256: n:nat -> Lemma
  (requires (n = 256))
  (ensures (pow2 n = 0x10000000000000000000000000000000000000000000000000000000000000000))
  [SMTPat (pow2 n)]
let lemma_pow2_256 n = assert_norm(pow2 256 = 0x10000000000000000000000000000000000000000000000000000000000000000)
