module Hacl.Spec.Poly1305.Lemmas

open FStar.Mul
module Scalar = Spec.Poly1305

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

//[@ "opaque_to_smt"]
let ( % ) (a:nat) (b:pos) : nat = a % b
let ( * ) (a:nat) (b:nat) : nat = a * b
let ( + ) (a:nat) (b:nat) : nat = a + b

private
val mul_mod1: a:nat -> b:nat -> p:pos -> Lemma
  (ensures ((a % p * (b % p)) % p == (a * b) % p))
  [SMTPat  ((a % p * (b % p)) % p)]
let mul_mod1 a b p =
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (a % p) b p;
  FStar.Math.Lemmas.lemma_mod_mul_distr_l a b p

private
val mul_mod2: a:nat -> b:nat -> p:pos -> Lemma
  (ensures ((a * (b % p)) % p == (a * b) % p))
  [SMTPat ((a * (b % p)) % p)]
let mul_mod2 a b p =
  FStar.Math.Lemmas.lemma_mod_mul_distr_r a b p

private
val mul_mod3: a:nat -> b:nat -> p:pos -> Lemma
  (ensures ((a % p * b) % p == (a * b) % p))
  [SMTPat ((a % p * b) % p)]
let mul_mod3 a b p =
  FStar.Math.Lemmas.lemma_mod_mul_distr_l a b p

private
val add_mod1: a:nat -> b:nat -> p:pos -> Lemma
  (ensures (((a % p) + (b % p)) % p == (a + b) % p))
  [SMTPat (((a % p) + (b % p)) % p)]
let add_mod1 a b p =
  FStar.Math.Lemmas.lemma_mod_plus_distr_l a (b % p) p;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r a b p

private
val add_mod2: a:nat -> b:nat -> p:pos -> Lemma
  (ensures (((a % p) + b) % p == (a + b) % p))
  [SMTPat (((a % p) + b) % p)]
let add_mod2 a b p =
  FStar.Math.Lemmas.lemma_mod_plus_distr_l a b p

private
val add_mod3: a:nat -> b:nat -> p:pos -> Lemma
  (ensures ((a + (b % p)) % p == (a + b) % p))
  [SMTPat ((a + (b % p)) % p)]
let add_mod3 a b p =
  FStar.Math.Lemmas.lemma_mod_plus_distr_r a b p

private
val add_mul1: a:nat -> b:nat -> c:nat -> Lemma
  (ensures ((a + b) * c == a * c + b * c))
  [SMTPat ((a + b) * c)]
let add_mul1 a b c = ()

private
val left_mul: a:nat -> b:nat -> c:nat -> Lemma
  (ensures (a * (b * c) == a * b * c))
  [SMTPat (a * (b * c))]
let left_mul a b c = ()

private
val left_add: a:nat -> b:nat -> c:nat -> Lemma
  (ensures (a + (b + c) == a + b + c))
  [SMTPat (a + (b + c))]
let left_add a b c = ()

let prime : pos = Scalar.prime
let pfelem = nat //x:nat{x < prime}
unfold let pfmul a b = (a * b) % prime
unfold let pfadd a b = (a + b) % prime

#reset-options "--z3refresh --z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val poly_update_repeat_blocks_multi_lemma2_simplify:
  acc0:pfelem -> acc1:pfelem -> c0:pfelem -> c1:pfelem -> r:pfelem -> Lemma
    (pfadd (pfmul (pfadd (pfmul acc0 (pfmul r r)) c0) (pfmul r r)) (pfmul (pfadd (pfmul acc1 (pfmul r r)) c1) r) ==
    pfmul (pfadd (pfmul (pfadd (pfadd (pfmul acc0 (pfmul r r)) (pfmul acc1 r)) c0) r) c1) r)
let poly_update_repeat_blocks_multi_lemma2_simplify acc0 acc1 c0 c1 r = ()

private
val add_mod4: a:nat -> b:nat -> c:nat -> d:nat -> p:pos -> Lemma
  (ensures ((a % p + b % p + c % p + d % p) % p == (a + b + c + d) % p))
let add_mod4 a b c d p =
  add_mod2 a (b % p + c % p + d % p) p;
  add_mod2 b (a + c % p + d % p) p;
  add_mod2 c (a + b + d % p) p;
  add_mod2 d (a + b + c) p

val poly_update_repeat_blocks_multi_lemma4_simplify_lp:
    a0r4:pfelem -> a1:pfelem -> a2:pfelem -> a3:pfelem
  -> c0:pfelem -> c1:pfelem -> c2:pfelem -> c3:pfelem
  -> r:pfelem ->
  Lemma (
    pfadd (pfadd (pfadd
     (pfmul (pfadd a0r4 c0) (pfmul (pfmul r r) (pfmul r r)))
     (pfmul (pfadd (pfmul a1 (pfmul (pfmul r r) (pfmul r r))) c1) (pfmul (pfmul r r) r)))
     (pfmul (pfadd (pfmul a2 (pfmul (pfmul r r) (pfmul r r))) c2) (pfmul r r)))
     (pfmul (pfadd (pfmul a3 (pfmul (pfmul r r) (pfmul r r))) c3) r) ==
     (a0r4 * r * r * r * r + c0 * r * r * r * r +
     a1 * r * r * r * r * r * r * r + c1 * r * r * r +
     a2 * r * r * r * r * r * r + c2 * r * r +
     a3 * r * r * r * r * r + c3 * r) % prime)
let poly_update_repeat_blocks_multi_lemma4_simplify_lp a0r4 a1 a2 a3 c0 c1 c2 c3 r =
  let p1 = a0r4 * r * r * r * r + c0 * r * r * r * r in
  let p2 = a1 * r * r * r * r * r * r * r + c1 * r * r * r in
  let p3 = a2 * r * r * r * r * r * r + c2 * r * r in
  let p4 = a3 * r * r * r * r * r + c3 * r in
  add_mod4 p1 p2 p3 p4 prime

val poly_update_repeat_blocks_multi_lemma4_simplify_rp:
    a0r4:pfelem -> a1:pfelem -> a2:pfelem -> a3:pfelem
  -> c0:pfelem -> c1:pfelem -> c2:pfelem -> c3:pfelem
  -> r:pfelem ->
  Lemma
   (pfmul (pfadd (pfmul (pfadd (pfmul (pfadd (pfmul (pfadd (pfadd (pfadd (pfadd a0r4
     (pfmul a1 (pfmul (pfmul r r) r))) (pfmul a2 (pfmul r r))) (pfmul a3 r)) c0) r) c1) r) c2) r) c3) r ==
   (a0r4 * r * r * r * r + a1 * r * r * r * r * r * r * r + a2 * r * r * r * r * r * r + a3 * r * r * r * r * r +
    c0 * r * r * r * r + c1 * r * r * r + c2 * r * r + c3 * r) % prime)
let poly_update_repeat_blocks_multi_lemma4_simplify_rp a0r4 a1 a2 a3 c0 c1 c2 c3 r =
  assert (
    pfmul (pfadd (pfmul (pfadd (pfmul (pfadd (pfmul (pfadd (pfadd (pfadd (pfadd a0r4
     (pfmul a1 (pfmul (pfmul r r) r))) (pfmul a2 (pfmul r r))) (pfmul a3 r)) c0) r) c1) r) c2) r) c3) r ==
    (a0r4 * r * r * r * r + a1 * r * r * r * r * r * r * r + a2 * r * r * r * r * r * r +
     a3 * r * r * r * r * r + c0 * r * r * r * r + c1 * r * r * r + c2 * r * r + c3 * r) % prime)

val poly_update_repeat_blocks_multi_lemma4_simplify_aux:
    a0:nat -> a1:nat -> a2:nat -> a3:nat
  -> a4:nat -> a5:nat -> a6:nat -> a7:nat ->
  Lemma (
    a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 ==
    a0 + a2 + a4 + a6 + a1 + a3 + a5 + a7)
let poly_update_repeat_blocks_multi_lemma4_simplify_aux a0 a1 a2 a3 a4 a5 a6 a7 = ()

val poly_update_repeat_blocks_multi_lemma4_simplify:
    a0r4:pfelem -> a1:pfelem -> a2:pfelem -> a3:pfelem
  -> c0:pfelem -> c1:pfelem -> c2:pfelem -> c3:pfelem
  -> r:pfelem ->
  Lemma
   (pfadd (pfadd (pfadd
     (pfmul (pfadd a0r4 c0) (pfmul (pfmul r r) (pfmul r r)))
     (pfmul (pfadd (pfmul a1 (pfmul (pfmul r r) (pfmul r r))) c1) (pfmul (pfmul r r) r)))
     (pfmul (pfadd (pfmul a2 (pfmul (pfmul r r) (pfmul r r))) c2) (pfmul r r)))
     (pfmul (pfadd (pfmul a3 (pfmul (pfmul r r) (pfmul r r))) c3) r) ==
    pfmul (pfadd (pfmul (pfadd (pfmul (pfadd (pfmul (pfadd (pfadd (pfadd (pfadd a0r4
	  (pfmul a1 (pfmul (pfmul r r) r))) (pfmul a2 (pfmul r r))) (pfmul a3 r)) c0) r) c1) r) c2) r) c3) r)
let poly_update_repeat_blocks_multi_lemma4_simplify a0r4 a1 a2 a3 c0 c1 c2 c3 r =
  poly_update_repeat_blocks_multi_lemma4_simplify_lp a0r4 a1 a2 a3 c0 c1 c2 c3 r;
  poly_update_repeat_blocks_multi_lemma4_simplify_rp a0r4 a1 a2 a3 c0 c1 c2 c3 r;
  poly_update_repeat_blocks_multi_lemma4_simplify_aux
    (a0r4 * r * r * r * r) (c0 * r * r * r * r) (a1 * r * r * r * r * r * r * r) (c1 * r * r * r)
    (a2 * r * r * r * r * r * r) (c2 * r * r) (a3 * r * r * r * r * r) (c3 * r)

val poly_update_multi_lemma_load2_simplify:
  acc0:pfelem -> r:pfelem -> c0:pfelem -> c1:pfelem ->
  Lemma
    (pfmul (pfadd (pfmul (pfadd acc0 c0) r) c1) r ==
     pfadd (pfmul (pfadd acc0 c0) (pfmul r r)) (pfmul c1 r))
let poly_update_multi_lemma_load2_simplify acc0 r c0 c1 = ()

val poly_update_multi_lemma_load4_simplify:
  acc0:pfelem -> r:pfelem -> c0:pfelem -> c1:pfelem -> c2:pfelem -> c3:pfelem ->
  Lemma
   (pfmul (pfadd (pfmul (pfadd (pfmul (pfadd (pfmul (pfadd acc0 c0) r) c1) r) c2) r) c3) r ==
     pfadd (pfadd (pfadd (pfmul (pfadd acc0 c0) (pfmul (pfmul r r) (pfmul r r)))
      (pfmul c1 (pfmul (pfmul r r) r))) (pfmul c2 (pfmul r r))) (pfmul c3 r))
let poly_update_multi_lemma_load4_simplify acc0 r c0 c1 c2 c3 = ()
