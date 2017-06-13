module Hacl.Impl.Ed25519.Verify.Lemmas

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul

let u51 = n:nat{n < 0x8000000000000}

val lemma_equality:
  a:u51 -> b:u51 -> c:u51 -> d:u51 -> e:u51 ->
  a':u51 -> b':u51 -> c':u51 -> d':u51 -> e':u51 ->
  Lemma (requires (a + pow2 51 * b + pow2 102 * c + pow2 153 * d + pow2 204 * e < pow2 255 - 19 /\
                   a' + pow2 51 * b' + pow2 102 * c' + pow2 153 * d' + pow2 204 * e' < pow2 255 - 19))
        (ensures (((a + pow2 51 * b + pow2 102 * c + pow2 153 * d + pow2 204 * e) % (pow2 255 - 19) = (a' + pow2 51 * b' + pow2 102 * c' + pow2 153 * d' + pow2 204 * e') % (pow2 255 - 19)) <==>
          (a == a' /\ b == b' /\ c == c' /\ d == d' /\ e == e')))

#reset-options "--max_fuel 0 --z3rlimit 500"

let lemma_equality a b c d e a' b' c' d' e' =
  assert_norm(pow2 51 = 0x8000000000000);
  assert_norm(pow2 102 = 0x40000000000000000000000000);
  assert_norm(pow2 153 = 0x200000000000000000000000000000000000000);
  assert_norm(pow2 204 = 0x1000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 255 - 19 = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed);
  Math.Lemmas.modulo_lemma (a + pow2 51 * b + pow2 102 * c + pow2 153 * d + pow2 204 * e) (pow2 255 - 19);
  Math.Lemmas.modulo_lemma (a' + pow2 51 * b' + pow2 102 * c' + pow2 153 * d' + pow2 204 * e') (pow2 255 - 19)

