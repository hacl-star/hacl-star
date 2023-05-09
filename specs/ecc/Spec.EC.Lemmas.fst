module Spec.EC.Lemmas

open FStar.Mul
open Spec.EC

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

let aff_point_at_inf_lemma (k:curve) (p:aff_point k) = ()

let aff_point_add_assoc_lemma (k:curve) (p q s:aff_point k) = admit()

let aff_point_add_comm_lemma (k:curve) (p q:aff_point k) = admit()


val lemma_eq_neg_value1: m:pos -> x:nat{x < m} -> Lemma
  (requires x = (-x) % m)
  (ensures  x = 0 || (x = m / 2 && m % 2 = 0))

let lemma_eq_neg_value1 m x =
  if x = 0 then ()
  else begin
    Math.Lemmas.lemma_mod_plus (-x) 1 m;
    assert ((-x + m) % m = (-x) % m);
    assert (m - x < m);
    Math.Lemmas.small_mod (m - x) m;
    assert ((-x) % m = m - x);
    assert (x = m - x);
    assert (2 * x = m);
    assert (x = m / 2);
    assert (m % 2 = 0) end


val lemma_eq_neg_value2: m:pos -> x:nat{x < m} -> Lemma
  (requires x = 0 || (x = m / 2 && m % 2 = 0))
  (ensures  x = (-x) % m)

let lemma_eq_neg_value2 m x =
  if x = 0 then ()
  else begin
    Math.Lemmas.lemma_mod_plus (-x) 1 m;
    assert ((-x + m) % m = (-x) % m);
    assert (m - x < m);
    Math.Lemmas.small_mod (m - x) m;
    assert ((-x) % m = m - x);
    assert (m - x = x);
    () end


val lemma_eq_neg_value: m:pos -> x:nat{x < m} ->
  Lemma (x = (-x) % m <==> (x = 0 \/ (x = m / 2 /\ m % 2 = 0)))

let lemma_eq_neg_value m x =
  Classical.move_requires (lemma_eq_neg_value1 m) x;
  Classical.move_requires (lemma_eq_neg_value2 m) x


val lemma_prime_mod_2_aux: p:pos{2 < p} -> Lemma
  (requires (~ (exists (q:nat). p = q * 2)))
  (ensures  p % 2 = 1)

let lemma_prime_mod_2_aux p =
  Math.Lemmas.euclidean_division_definition p 2


val lemma_prime_mod_2: p:pos -> Lemma
  (requires 2 < p /\ FStar.Math.Euclid.is_prime p)
  (ensures  p % 2 = 1)

let lemma_prime_mod_2 p =
  let open FStar.Math.Euclid in
  assert (is_prime p);
  assert (forall (d:int). (d `divides` p ==> (d = 1 \/ d = -1 \/ d = p \/ d = -p)));
  assert (~ (2 `divides` p));
  assert (~ (exists q. p = q * 2));
  lemma_prime_mod_2_aux p


val lemma_eq_neg_value_prime: m:pos{2 < m /\ Math.Euclid.is_prime m} -> x:nat{x < m} ->
  Lemma (x = (-x) % m <==> (x = 0))

let lemma_eq_neg_value_prime m x =
  lemma_prime_mod_2 m


let aff_point_negate_lemma (k:curve) (p:aff_point k) =
  let p_neg = aff_point_negate k p in
  let px, py = p_neg in
  let qx, qy = p in
  assert (px = qx /\ py = (-qy) % prime);
  let res = aff_point_add k p_neg p in

  if is_aff_point_at_inf k p_neg then ()
  else begin
    if is_aff_point_at_inf k p then ()
    else begin
    if p_neg = p then begin
      assert (py = qy);
      assert (qy = (-qy) % prime);
      prime_lemma ();
      lemma_eq_neg_value_prime prime qy end
    else () end
  end
