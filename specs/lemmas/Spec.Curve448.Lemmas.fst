module Spec.Curve448.Lemmas

val lemma_prime_value: x:nat -> y:nat -> Lemma
  (requires (x = 448 /\ y = 224))
  (ensures (pow2 x - pow2 y - 1 = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffffffffffffffffffffffffffffffffffffffffffffffffffff))
  [SMTPat (pow2 x - pow2 y - 1)]

let lemma_prime_value x y =
  assert_norm(pow2 448 - pow2 224 - 1 = 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439)

val lemma_div_n: n:nat -> Lemma
  (requires (n > 1))
  (ensures (n / 2 < n /\ n / 2 > 0))
  [SMTPat (n / 2)]
let lemma_div_n n = ()

val lemma_pow2_448: n:nat -> Lemma
  (requires (n = 448))
  (ensures (pow2 n = 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
  [SMTPat (pow2 n)]
let lemma_pow2_448 n = assert_norm(pow2 448 = 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
