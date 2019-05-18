module Vale.Math.Lemmas.Int
open FStar.Mul

#reset-options "--initial_fuel 0 --max_fuel 0 --z3cliopt smt.arith.nl=true --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"

let multiply_fractions (a:int) (n:pos) = ()
let lemma_div_mod (a:int) (n:pos) = ()

let lemma_div_lt a n m =
  if a >= 0 then FStar.Math.Lemmas.lemma_div_lt a n m
  else ()

let bounded_multiple_is_zero (x:int) (n:pos) = ()

let small_div (a:nat) (n:pos) : Lemma (requires a < n) (ensures a / n == 0) = ()
let small_mod (a:nat) (n:pos) : Lemma (requires a < n) (ensures a % n == a) = ()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3cliopt smt.arith.nl=false --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped"

let lt_multiple_is_equal (a:nat) (b:nat) (x:int) (n:pos) =
  assert (0 * n == 0);
  bounded_multiple_is_zero x n

let add_div_mod_1 (a:int) (n:pos) : Lemma ((a + n) % n == a % n /\ (a + n) / n == a / n + 1) =
  lemma_div_mod a n;
  lemma_div_mod (a + n) n;
  // ((a + n) % n) == a % n + (a / n) * n + n - ((a + n) / n) * n
  FStar.Math.Lemmas.distributivity_add_left (a / n) 1 n;
  FStar.Math.Lemmas.distributivity_sub_left (a / n + 1) ((a + n) / n) n;
  // (((a + n) % n) == a % n + (a / n + 1 - (a + n) / n) * n
  lt_multiple_is_equal ((a + n) % n) (a % n) (a / n + 1 - (a + n) / n) n;
  ()

let sub_div_mod_1 (a:int) (n:pos) : Lemma ((a - n) % n == a % n /\ (a - n) / n == a / n - 1) =
  lemma_div_mod a n;
  lemma_div_mod (a - n) n;
  // ((a - n) % n) == a % n - n + (a / n) * n - ((a - n) / n) * n
  FStar.Math.Lemmas.distributivity_add_left (a / n) 1 n;
  FStar.Math.Lemmas.distributivity_sub_left (a / n - 1) ((a - n) / n) n;
  // ((a - n) % n) == a % n + (a / n - 1 - (a - n) / n) * n
  lt_multiple_is_equal ((a - n) % n) (a % n) (a / n - 1 - (a - n) / n) n;
  ()

let rec lemma_div_mod_plus (a:int) (b:int) (n:pos) : Lemma
  (requires True)
  (ensures
    (a + b * n) / n = a / n + b /\
    (a + b * n) % n = a % n
  )
  (decreases (if b > 0 then b else -b))
  =
  if b = 0 then ()
  else if b > 0 then
  (
    lemma_div_mod_plus a (b - 1) n;
    sub_div_mod_1 (a + b * n) n
  )
  else // b < 0
  (
    lemma_div_mod_plus a (b + 1) n;
    add_div_mod_1 (a + b * n) n
  )

let lemma_div_plus (a:int) (b:int) (n:pos) = lemma_div_mod_plus a b n
let lemma_mod_plus (a:int) (b:int) (n:pos) = lemma_div_mod_plus a b n

let cancel_mul_div (a:int) (n:pos) =
  small_div 0 n;
  lemma_div_plus 0 a n

let cancel_mul_mod (a:int) (n:pos) =
  small_mod 0 n;
  lemma_mod_plus 0 a n

let mod_add_both (a:int) (b:int) (x:int) (n:pos) =
  lemma_div_mod a n;
  lemma_div_mod b n;
  lemma_div_mod (a + x) n;
  lemma_div_mod (b + x) n;
  let xx = (b + x) / n - (a + x) / n - b / n + a / n in
  FStar.Math.Lemmas.distributivity_sub_left ((b + x) / n) ((a + x) / n) n;
  FStar.Math.Lemmas.distributivity_sub_left ((b + x) / n - (a + x) / n) (b / n) n;
  FStar.Math.Lemmas.distributivity_add_left ((b + x) / n - (a + x) / n - b / n) (a / n) n;
  lt_multiple_is_equal ((a + x) % n) ((b + x) % n) xx n

let lemma_mod_add_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  // (a + b) % n == (a + (b % n) + (b / n) * n) % n
  lemma_mod_plus (a + (b % n)) (b / n) n

let lemma_mod_sub_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  FStar.Math.Lemmas.distributivity_sub_left 0 (b / n) n;
  // (a - b) % n == (a - (b % n) - (b / n) * n) % n
  lemma_mod_plus (a - (b % n)) (-(b / n)) n

let rec lemma_mod_mul_distr_l (a:int) (b:int) (n:pos) =
  if b = 0 then
  (
    assert (a * 0 == 0 /\ ((a % n) * 0) == 0);
    small_mod 0 n
  )
  else if b > 0 then
  (
    lemma_mod_mul_distr_l a (b - 1) n;
    FStar.Math.Lemmas.distributivity_sub_right a b 1;
    FStar.Math.Lemmas.distributivity_sub_right (a % n) b 1;
    // (a * b - a) % n == ((a % n) * b - (a % n)) % n
    lemma_mod_sub_distr ((a % n) * b) a n;
    // (a * b - a) % n = ((a % n) * b - a) % n
    mod_add_both (a * b - a) ((a % n) * b - a) a n
  )
  else
  (
    lemma_mod_mul_distr_l a (b + 1) n;
    FStar.Math.Lemmas.distributivity_add_right a b 1;
    FStar.Math.Lemmas.distributivity_add_right (a % n) b 1;
    // (a * b + a) % n == ((a % n) * b + (a % n)) % n
    lemma_mod_add_distr ((a % n) * b) a n;
    // (a * b + a) % n = ((a % n) * b + a) % n
    mod_add_both (a * b + a) ((a % n) * b + a) (-a) n
  )

let lemma_mod_mul_distr_r (a:int) (b:int) (n:pos) = lemma_mod_mul_distr_l b a n
let lemma_div_exact (a:int) (n:pos) = lemma_div_mod a n
let div_exact_r (a:int) (n:pos) = lemma_div_exact a n

let lemma_mod_spec (a:int) (n:pos) =
  lemma_div_mod a n;
  lemma_div_mod (a - (a % n)) n;
  small_mod 0 n;
  lemma_mod_sub_distr a a n; // (a - a % n) % n = (a - a) % n = 0 % n = 0
  // (a / n) * n == ((a - a % n) / n) * n
  cancel_mul_div (a / n) n;
  cancel_mul_div ((a - a % n) / n) n

let lemma_mod_spec2 (a:int) (n:pos) =
  lemma_div_mod a n;
  lemma_mod_spec a n

let lemma_mod_plus_distr_l (a:int) (b:int) (n:pos) = lemma_mod_add_distr b a n
let lemma_mod_plus_distr_r (a:int) (b:int) (n:pos) = lemma_mod_add_distr a b n

let small_division_lemma_2 (a:int) (n:pos) = lemma_div_mod a n

#reset-options "--initial_fuel 0 --max_fuel 0 --z3cliopt smt.arith.nl=true --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"
let multiplication_order_lemma a b n = ()
#reset-options "--initial_fuel 0 --max_fuel 0 --z3cliopt smt.arith.nl=false --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped"

let division_propriety (a:int) (n:pos) = lemma_div_mod a n

let division_definition (a:int) (n:pos) (m:int) =
  lemma_div_mod a n;
  FStar.Math.Lemmas.distributivity_sub_left (a / n) m n;
  bounded_multiple_is_zero (a / n - m) n

let multiple_division_lemma (a:int) (n:pos) = cancel_mul_div a n
let multiple_modulo_lemma (a:int) (n:pos) = cancel_mul_mod a n
let division_addition_lemma (a:int) (n:pos) (b:int) = lemma_div_plus a b n
let division_sub_lemma (a:nat) (n:pos) (b:nat) = lemma_div_plus a (-b) n

#reset-options "--initial_fuel 0 --max_fuel 0 --z3cliopt smt.arith.nl=true --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"

let modulo_distributivity (a:int) (b:int) (c:pos) =
  lemma_div_mod a c;
  lemma_div_mod b c;
  lemma_div_mod (a % c + b % c) c;
  division_addition_lemma  (a - (a / c) * c + b - (b / c) * c) c (a / c + b / c)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3cliopt smt.arith.nl=false --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped"


let modulo_addition_lemma (a:int) (n:pos) (b:int) = lemma_mod_plus a b n
let lemma_mod_sub (a:int) (n:pos) (b:nat) = lemma_mod_plus a (-b) n

let mod_mult_exact (a:int) (n:pos) (q:pos) =
  FStar.Math.Lemmas.pos_times_pos_is_pos n q;
  lemma_div_mod a (n * q);
  let k = a / (n * q) in
  FStar.Math.Lemmas.paren_mul_right k q n;
  // a == (k * q) * n
  cancel_mul_mod (k * q) n

let mod_mul_div_exact (a:int) (b:pos) (n:pos) =
  FStar.Math.Lemmas.pos_times_pos_is_pos b n;
  lemma_div_mod a (b * n);
  let k = a / (b * n) in
  FStar.Math.Lemmas.paren_mul_right k n b;
  // a == (k * n) * b
  cancel_mul_div (k * n) b;
  // a / b = k * n
  cancel_mul_mod k n

#reset-options "--initial_fuel 1 --max_fuel 1 --z3cliopt smt.arith.nl=false --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped"
let mod_pow2_div2 (a:int) (m:pos) : Lemma
  (requires a % pow2 m == 0)
  (ensures (a / 2) % pow2 (m - 1) == 0)
  =
  mod_mul_div_exact a 2 (pow2 (m - 1))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3cliopt smt.arith.nl=false --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped"

let division_multiplication_lemma (a:int) (b:pos) (c:pos) =
  FStar.Math.Lemmas.pos_times_pos_is_pos b c;
  lemma_div_mod a b;
  lemma_div_mod (a / b) c;
  lemma_div_mod a (b * c);
  let k1 = a / b - ((a / b) / c) * c in // k1 = (a / b) % c
  let k2 = a - (a / (b * c)) * (b * c) in // k2 = a % (b * c)
  FStar.Math.Lemmas.distributivity_sub_left (a / b) (((a / b) / c) * c) b;
  FStar.Math.Lemmas.paren_mul_right ((a / b) / c) c b;
  FStar.Math.Lemmas.swap_mul b c;
  // k1 * b == (a / b) * b - ((a / b) / c) * (b * c)
  // k1 * b - k2 == (a / (b * c) - (a / b) / c) * (b * c) - a % b
  FStar.Math.Lemmas.lemma_mult_le_right b 0 k1;
  FStar.Math.Lemmas.lemma_mult_le_right b k1 (c - 1);
  FStar.Math.Lemmas.distributivity_sub_left c 1 b;
  // 0 <= k1 <= (c - 1)
  // 0 <= k1 * b <= (c - 1) * b
  // 0 <= k2 < b * c
  // 1 - b * c <= k1 * b - k2 <= b * c - b
  FStar.Math.Lemmas.distributivity_sub_left (a / (b * c)) ((a / b) / c) (b * c);
  bounded_multiple_is_zero (a / (b * c) - (a / b) / c) (b * c)

let modulo_modulo_lemma (a:int) (b:pos) (c:pos) =
  FStar.Math.Lemmas.pos_times_pos_is_pos b c;
  lemma_div_mod a (b * c);
  FStar.Math.Lemmas.paren_mul_right (a / (b * c)) c b;
  FStar.Math.Lemmas.swap_mul b c;
  lemma_mod_plus (a % (b * c)) ((a / (b * c)) * c) b

let lemma_mod_plus_injective (n:pos) (a:int) (b:nat) (c:nat) =
  small_mod b n;
  small_mod c n;
  mod_add_both (a + b) (a + c) (-a) n
