module Vale.Math.Lemmas.Int
// This module generalizes lemmas in FStar.Math.Lemmas to use int rather than nat.
// For more stable verification, most lemmas are proven with smt.arith.nl=false.
open FStar.Mul

val multiply_fractions (a:int) (n:pos) : Lemma (n * ( a / n ) <= a)

val lemma_div_mod (a:int) (n:pos) : Lemma (a == (a / n) * n + a % n)

val lemma_div_lt (a:int) (n:nat) (m:nat) : Lemma
  (requires m <= n /\ a < pow2 n)
        (ensures a / pow2 m < pow2 (n-m))

val bounded_multiple_is_zero (x:int) (n:pos) : Lemma
  (requires -n < x * n /\ x * n < n)
  (ensures x == 0)

val small_div (a:nat) (n:pos) : Lemma (requires a < n) (ensures a / n == 0)
val small_mod (a:nat) (n:pos) : Lemma (requires a < n) (ensures a % n == a)

val lt_multiple_is_equal (a:nat) (b:nat) (x:int) (n:pos) : Lemma
  (requires a < n /\ b < n /\ a == b + x * n)
  (ensures a == b /\ x == 0)

val lemma_div_plus (a:int) (b:int) (n:pos) : Lemma ((a + b * n) / n = a / n + b)
val lemma_mod_plus (a:int) (b:int) (n:pos) : Lemma ((a + b * n) % n = a % n)
val cancel_mul_div (a:int) (n:pos) : Lemma ((a * n) / n == a)
val cancel_mul_mod (a:int) (n:pos) : Lemma ((a * n) % n == 0)

val mod_add_both (a:int) (b:int) (x:int) (n:pos) : Lemma
  (requires a % n == b % n)
  (ensures (a + x) % n == (b + x) % n)

val lemma_mod_add_distr (a:int) (b:int) (n:pos) : Lemma ((a + b % n) % n = (a + b) % n)
val lemma_mod_sub_distr (a:int) (b:int) (n:pos) : Lemma ((a - b % n) % n = (a - b) % n)

val lemma_mod_mul_distr_l (a:int) (b:int) (n:pos) : Lemma
  (requires True)
  (ensures (a * b) % n = ((a % n) * b) % n)
  (decreases (if b >= 0 then b else -b))

val lemma_mod_mul_distr_r (a:int) (b:int) (n:pos) : Lemma ((a * b) % n = (a * (b % n)) % n)

val lemma_div_exact (a:int) (n:pos) : Lemma
  (requires (a % n = 0))
  (ensures  (a = n * (a / n)))

val div_exact_r (a:int) (n:pos) : Lemma
  (requires (a % n = 0))
  (ensures  (a = (a / n) * n))

val lemma_mod_spec (a:int) (n:pos) : Lemma (a / n = (a - a % n) / n)
val lemma_mod_spec2 (a:int) (n:pos) : Lemma (let q = (a - (a % n)) / n in a = (a % n) + q * n)
val lemma_mod_plus_distr_l (a:int) (b:int) (n:pos) : Lemma ((a + b) % n = ((a % n) + b) % n)
val lemma_mod_plus_distr_r (a:int) (b:int) (n:pos) : Lemma ((a + b) % n = (a + (b % n)) % n)

val small_division_lemma_2 (a:int) (n:pos) : Lemma
  (requires a / n = 0)
  (ensures 0 <= a /\ a < n)

val multiplication_order_lemma (a:int) (b:int) (n:pos) : Lemma (a >= b <==> a * n >= b * n)
val division_propriety (a:int) (n:pos) : Lemma (a - n < (a / n) * n /\ (a / n) * n <= a)

val division_definition (a:int) (n:pos) (m:int) : Lemma
  (requires a - n < m * n /\ m * n <= a)
  (ensures m = a / n)

val multiple_division_lemma (a:int) (n:pos) : Lemma ((a * n) / n = a)
val multiple_modulo_lemma (a:int) (n:pos) : Lemma ((a * n) % n = 0)
val division_addition_lemma (a:int) (n:pos) (b:int) : Lemma ((a + b * n) / n = a / n + b)
val division_sub_lemma (a:nat) (n:pos) (b:nat) : Lemma ((a - b * n) / n = a / n - b)

val modulo_distributivity: a:int -> b:int -> c:pos ->
    Lemma ( (a + b) % c = (a % c + b % c) % c )

val modulo_addition_lemma (a:int) (n:pos) (b:int) : Lemma ((a + b * n) % n = a % n)
val lemma_mod_sub (a:int) (n:pos) (b:nat) : Lemma (ensures (a - b * n) % n = a % n)

val mod_mult_exact (a:int) (n:pos) (q:pos) : Lemma
  (requires (FStar.Math.Lemmas.pos_times_pos_is_pos n q; a % (n * q) == 0))
  (ensures a % n == 0)

val mod_mul_div_exact (a:int) (b:pos) (n:pos) : Lemma
  (requires (FStar.Math.Lemmas.pos_times_pos_is_pos b n; a % (b * n) == 0))
  (ensures (a / b) % n == 0)

val mod_pow2_div2 (a:int) (m:pos) : Lemma
  (requires a % pow2 m == 0)
  (ensures (a / 2) % pow2 (m - 1) == 0)

val division_multiplication_lemma (a:int) (b:pos) (c:pos) : Lemma
  (FStar.Math.Lemmas.pos_times_pos_is_pos b c; a / (b * c) = (a / b) / c)

val modulo_modulo_lemma (a:int) (b:pos) (c:pos) : Lemma
  (FStar.Math.Lemmas.pos_times_pos_is_pos b c; (a % (b * c)) % b = a % b)

// OMITTED: pow2 lemmas

val lemma_mod_plus_injective (n:pos) (a:int) (b:nat) (c:nat) : Lemma
  (requires b < n /\ c < n /\ (a + b) % n = (a + c) % n)
  (ensures  b = c)

