module Hacl.Spec.Poly1305.Lemmas

open FStar.Mul
module Scalar = Spec.Poly1305

open FStar.Algebra.CommMonoid
open FStar.Tactics.CanonCommSemiring

/// Semiring for Poly1305

#set-options "--z3rlimit 5 --max_fuel 0 --max_ifuel 0 --z3cliopt smt.arith.nl=false"

let prime: pos = Scalar.prime

let pfelem : eqtype = a:nat{a < prime}

[@canon_attr]
let zero : pfelem = 0

[@canon_attr]
let one : pfelem = normalize_term_spec prime; 1

//[@(strict_on_arguments [0;1])]
let ( +% ) (a b:pfelem) : pfelem = (a + b) % prime

//[@(strict_on_arguments [0;1])]
let ( *% ) (a b:pfelem) : pfelem = (a * b) % prime

val add_identity: a:pfelem -> Lemma (zero +% a == a)
let add_identity a = normalize_term_spec prime

val mul_identity: a:pfelem -> Lemma (one *% a == a)
let mul_identity a = normalize_term_spec prime

val add_associativity: a:pfelem -> b:pfelem -> c:pfelem
  -> Lemma (a +% b +% c == a +% (b +% c))
let add_associativity a b c =
  normalize_term_spec prime;
  calc (==) {
    a +% b +% c;
    == { }
    ((a + b) % prime + c) % prime;
    == { Math.Lemmas.lemma_mod_plus_distr_l (a + b) c prime }
    ((a + b) + c) % prime;
    == { }
    (a + (b + c)) % prime;
    == { Math.Lemmas.lemma_mod_plus_distr_r a (b + c) prime }
    a +% (b +% c);
  }

val add_commutativity: a:pfelem -> b:pfelem -> Lemma (a +% b == b +% a)
let add_commutativity a b = ()

val mul_associativity: a:pfelem -> b:pfelem -> c:pfelem
  -> Lemma (a *% b *% c == a *% (b *% c))
let mul_associativity a b c =
  calc (==) {
    a *% b *% c;
    == { }
    (((a * b) % prime) * c) % prime;
    == { Math.Lemmas.lemma_mod_mul_distr_l (a * b) c prime }
    ((a * b) * c) % prime;
    == { Math.Lemmas.paren_mul_right a b c }
    (a * (b * c)) % prime;
    == { Math.Lemmas.lemma_mod_mul_distr_r a (b * c) prime }
    (a * ((b * c) % prime)) % prime;
    == { }
    a *% (b *% c);
  }

val mul_commutativity: a:pfelem -> b:pfelem -> Lemma (a *% b == b *% a)
let mul_commutativity a b = ()

[@canon_attr]
let pfelem_add_cm : cm pfelem =
  CM zero ( +% ) add_identity add_associativity add_commutativity

[@canon_attr]
let pfelem_mul_cm : cm pfelem =
  CM one ( *% ) mul_identity mul_associativity mul_commutativity

val mul_add_distr: distribute_left_lemma pfelem pfelem_add_cm pfelem_mul_cm
let mul_add_distr a b c =
  normalize_term_spec prime;
  calc (==) {
    a *% (b +% c);
    == { }
    (a * (b +% c)) % prime;
    == { Math.Lemmas.lemma_mod_add_distr a (b + c) prime }
    (a * ((b + c) % prime)) % prime;
    == { Math.Lemmas.lemma_mod_mul_distr_r a (b + c) prime }
    (a * (b + c)) % prime;
    == { Math.Lemmas.distributivity_add_right a b c }
    (a * b + a * c) % prime;
    == { Math.Lemmas.lemma_mod_add_distr (a * b) (a * c) prime }
    (a * b + a *% c) % prime;
    == { }
    (a *% c + a * b) % prime;
    == { Math.Lemmas.lemma_mod_add_distr (a *% c) (a * b) prime }
    (a *% c + a *% b) % prime;
    == { }
    (a *% b + a *% c) % prime;
    == { }
    a *% b +% a *% c;
  }

val mul_zero_l: mult_zero_l_lemma pfelem pfelem_add_cm pfelem_mul_cm
let mul_zero_l a = assert_norm (forall x. zero *% x == zero)

[@canon_attr]
let pfelem_cr : cr pfelem = CR pfelem_add_cm pfelem_mul_cm mul_add_distr mul_zero_l

open FStar.Tactics

let poly_semiring () : Tac unit = canon_semiring pfelem_cr


/// Lemmas

val poly_update_repeat_blocks_multi_lemma2_simplify:
  acc0:pfelem -> acc1:pfelem -> c0:pfelem -> c1:pfelem -> r:pfelem ->
  Lemma (
     (acc0 *% (r *% r) +% c0) *% (r *% r) +% (acc1 *% (r *% r) +% c1) *% r ==
     ((((acc0 *% (r *% r) +% acc1 *% r) +% c0) *% r) +% c1) *% r )
let poly_update_repeat_blocks_multi_lemma2_simplify acc0 acc1 c0 c1 r =
  assert (
    (acc0 *% (r *% r) +% c0) *% (r *% r) +% (acc1 *% (r *% r) +% c1) *% r ==
    ((((acc0 *% (r *% r) +% acc1 *% r) +% c0) *% r) +% c1) *% r )
  by (poly_semiring ())

val poly_update_repeat_blocks_multi_lemma4_simplify:
    a0:pfelem -> a1:pfelem -> a2:pfelem -> a3:pfelem
  -> c0:pfelem -> c1:pfelem -> c2:pfelem -> c3:pfelem
  -> r:pfelem -> r2:pfelem{r2 == r *% r} -> r4:pfelem {r4 == r2 *% r2} ->
  Lemma
   (((a0 *% r4 +% c0) *% r4) +%
    ((a1 *% r4 +% c1) *% (r2 *% r)) +%
    ((a2 *% r4 +% c2) *% r2) +%
    ((a3 *% r4 +% c3) *% r)
    ==
    (((((((((((a0 *% r4 +%
      (a1 *% (r2 *% r))) +%
        a2 *% r2) +%
          a3 *% r) +% c0) *% r) +% c1) *% r) +% c2) *% r) +% c3) *% r) )
let poly_update_repeat_blocks_multi_lemma4_simplify a0 a1 a2 a3 c0 c1 c2 c3 r r2 r4 =
  let r2 = r *% r in
  let r4 = r2 *% r2 in
  assert (
    ((a0 *% r4 +% c0) *% r4) +%
    ((a1 *% r4 +% c1) *% (r2 *% r)) +%
    ((a2 *% r4 +% c2) *% r2) +%
    ((a3 *% r4 +% c3) *% r)
    ==
    (((((((((((a0 *% r4 +%
      (a1 *% (r2 *% r))) +%
        a2 *% r2) +%
          a3 *% r) +% c0) *% r) +% c1) *% r) +% c2) *% r) +% c3) *% r) )
  by (poly_semiring ())

val poly_update_multi_lemma_load2_simplify:
  acc0:pfelem -> r:pfelem -> c0:pfelem -> c1:pfelem ->
  Lemma
  ( (((acc0 +% c0) *% r) +% c1) *% r ==
    ((acc0 +% c0) *% (r *% r)) +% c1 *% r )
let poly_update_multi_lemma_load2_simplify acc0 r c0 c1 =
  assert (
    (((acc0 +% c0) *% r) +% c1) *% r ==
    ((acc0 +% c0) *% (r *% r)) +% c1 *% r )
  by (poly_semiring ())

val poly_update_multi_lemma_load4_simplify:
  acc0:pfelem -> r:pfelem -> c0:pfelem -> c1:pfelem -> c2:pfelem -> c3:pfelem ->
  Lemma
   ( (((((((acc0 +% c0) *% r) +% c1) *% r) +% c2) *% r) +% c3) *% r ==
     ((((acc0 +% c0) *% ((r *% r) *% (r *% r))) +%
      (c1 *% ((r *% r) *% r))) +% (c2 *% (r *% r))) +% c3 *% r )
let poly_update_multi_lemma_load4_simplify acc0 r c0 c1 c2 c3 =
  assert (
   (((((((acc0 +% c0) *% r) +% c1) *% r) +% c2) *% r) +% c3) *% r ==
   ((((acc0 +% c0) *% ((r *% r) *% (r *% r))) +%
     (c1 *% ((r *% r) *% r))) +% (c2 *% (r *% r))) +% c3 *% r )
  by (poly_semiring ())
