module Vale.Math.Poly2
open FStar.Mul
open FStar.Seq
open Vale.Math.Poly2_s

// Fundamental lemmas
// (derived lemmas should go in Vale.Math.Poly2.Lemmas_i)

unfold let ( +. ) = add
unfold let ( *. ) = mul
unfold let ( /. ) = div
unfold let ( %. ) = mod

let size (a:poly) : int = degree a + 1

val poly_and (a:poly) (b:poly) : poly
val poly_or (a:poly) (b:poly) : poly

// Keep terms up to degree < n, drop terms of degree >= n
val mask (a:poly) (n:nat) : poly

let swap (a:poly) (n:nat) : poly =
  shift (mask a n) n +. shift a (-n)

// n 1 bits (ones.[0] && ... && ones.[n - 1])
val ones (n:nat) : poly

let rec power (a:poly) (n:nat) : poly =
  if n = 0 then one else a *. power a (n - 1)

val lemma_degree_at_least (a:poly) : Lemma
  (requires True)
  (ensures degree a >= -1)
  [SMTPat (degree a)]

val lemma_equal (a b:poly) : Lemma (requires (forall (i:int). a.[i] == b.[i])) (ensures a == b)
val lemma_index_i (a:poly) (i:int) : Lemma (a.[i] ==> 0 <= i /\ i <= degree a)
val lemma_degree (a:poly) : Lemma (degree a == (-1) \/ a.[degree a])

val lemma_zero_define_i (i:int) : Lemma (not zero.[i])
val lemma_one_define_i (i:int) : Lemma (one.[i] == (i = 0))
val lemma_monomial_define_i (n:nat) (i:int) : Lemma ((monomial n).[i] == (i = n))
val lemma_shift_define_i (p:poly) (n:int) (i:int) : Lemma ((shift p n).[i] == (p.[i - n] && i >= 0))
val lemma_and_define_i (a b:poly) (i:int) : Lemma ((poly_and a b).[i] == (a.[i] && b.[i]))
val lemma_or_define_i (a b:poly) (i:int) : Lemma ((poly_or a b).[i] == (a.[i] || b.[i]))
val lemma_mask_define_i (p:poly) (n:nat) (i:int) : Lemma ((mask p n).[i] == (p.[i] && i < n))
val lemma_ones_define_i (n:nat) (i:int) : Lemma ((ones n).[i] == (0 <= i && i < n))
val lemma_reverse_define_i (p:poly) (n:nat) (i:int) : Lemma ((reverse p n).[i] == (p.[n - i] && i >= 0))

val lemma_add_zero (a:poly) : Lemma ((a +. zero) == a)
val lemma_add_cancel (a:poly) : Lemma ((a +. a) == zero)
val lemma_add_cancel_eq (a b:poly) : Lemma (requires (a +. b) == zero) (ensures a == b)
val lemma_add_commute (a b:poly) : Lemma ((a +. b) == (b +. a))
val lemma_add_associate (a b c:poly) : Lemma ((a +. (b +. c)) == ((a +. b) +. c))
val lemma_add_define_i (a b:poly) (i:int) : Lemma ((a +. b).[i] == (a.[i] <> b.[i]))
val lemma_add_degree (a b:poly) : Lemma
  (degree (a +. b) <= degree a \/ degree (a +. b) <= degree b)
  [SMTPat (degree (a +. b))]

val lemma_mul_zero (a:poly) : Lemma ((a *. zero) == zero)
val lemma_mul_one (a:poly) : Lemma ((a *. one) == a)
val lemma_mul_commute (a b:poly) : Lemma ((a *. b) == (b *. a))
val lemma_mul_associate (a b c:poly) : Lemma (a *. (b *. c) == (a *. b) *. c)
val lemma_mul_distribute (a b c:poly) : Lemma (a *. (b +. c) == (a *. b) +. (a *. c))
val lemma_mul_degree (a b:poly) : Lemma
  (degree (a *. b) == (if degree a >= 0 && degree b >= 0 then degree a + degree b else -1))
  [SMTPat (degree (a *. b))]
val lemma_mul_reverse (a b:poly) (n:nat) : Lemma
  (requires degree a <= n /\ degree b <= n)
  (ensures reverse (a *. b) (n + n) == reverse a n *. reverse b n)

val lemma_shift_is_mul (a:poly) (n:nat) : Lemma (shift a n == a *. (monomial n))

val lemma_div_mod (a b:poly) : Lemma
  (requires degree b >= 0)
  (ensures a == (a /. b) *. b +. (a %. b))

val lemma_div_degree (a b:poly) : Lemma
  (requires degree b >= 0)
  (ensures degree (a /. b) == (if degree a < degree b then -1 else degree a - degree b))
  [SMTPat (degree (a /. b))]

val lemma_mod_degree (a b:poly) : Lemma
  (requires degree b >= 0)
  (ensures degree (a %. b) < degree b)
  [SMTPat (degree (a %. b))]
