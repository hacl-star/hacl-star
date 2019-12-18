module Vale.Poly1305.Math

open FStar.Tactics
open FStar.Tactics.Canon
open FStar.Math.Lemmas
// open FStar.Math.Lib
open Vale.Math.Lemmas.Int
open FStar.Tactics.CanonCommSemiring
open FStar.Mul
open Vale.Def.TypesNative_s
open Vale.Arch.TypesNative
open FStar.Classical
open Vale.Poly1305.Bitvectors

#reset-options "--smtencoding.elim_box true --z3cliopt smt.arith.nl=true --max_fuel 1 --max_ifuel 1 --smtencoding.nl_arith_repr native --z3rlimit 100 --using_facts_from Prims --using_facts_from FStar.Math.Lemmas"

val lemma_mul_div_comm: a:nat -> b:pos -> c:nat ->
    Lemma (requires (c % b = 0 /\ a % b = 0))
          (ensures (a/b)*c == a * (c/b))
let lemma_mul_div_comm a b c =
    ()

val lemma_exact_mul: a:nat -> b:pos -> c:nat ->
    Lemma (requires (c % b = 0))
          (ensures ((a*c) % b = 0))
let lemma_exact_mul a b c =
  (* a*c = c*a *)
  swap_mul a c;

  (* (c*a)%b = ((c%b)*a)%b *)
  lemma_mod_mul_distr_l c a b;
  ()

val lemma_mul_div_sep: a:nat -> b:pos -> c:nat ->
    Lemma (requires (c % b = 0) /\ (a*c) % b = 0)
          (ensures (a*c)/b == a * (c/b))
let lemma_mul_div_sep a b c = ()

val swap_add: a:int -> b:int -> c:int -> Lemma
      (a + b + c = a + c + b)
let swap_add a b c = ()

#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=true --max_fuel 0 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 15"

let lemma_mul_increases(x y:pos) :
  Lemma (y <= y * x) = ()

val multiplication_order_lemma_int: a:int -> b:int -> p:pos ->
    Lemma (a < b <==> p * a < p * b)
let multiplication_order_lemma_int a b p = ()

val multiplication_order_eq_lemma_int: a:int -> b:int -> p:pos ->
    Lemma (a <= b <==> p * a <= p * b)
let multiplication_order_eq_lemma_int a b p = ()

#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 8"

let lemma_poly_multiply (n:int) (p:int) (r:int) (h:int) (r0:int) (r1:int) (h0:int) (h1:int)
                        (h2:int) (s1:int) (d0:int) (d1:int) (d2:int) (hh:int) =
  let r1_4 = r1 / 4 in
  let h_r_expand = (h2 * (n * n) + h1 * n + h0) * ((r1_4 * 4) * n + r0) in
  let hh_expand = (h2 * r0) * (n * n) + (h0 * (r1_4 * 4) + h1 * r0 + h2 * (5 * r1_4)) * n
    + (h0 * r0 + h1 * (5 * r1_4)) in
  //assert (h * r == h_r_expand);
  //assert (hh == hh_expand);
  let b = ((h2 * n + h1) * r1_4) in
  modulo_addition_lemma hh_expand p b;
  assert (h_r_expand == hh_expand + b * (n * n * 4 + (-5)))
  by (int_semiring ())


let lemma_poly_reduce (n:int) (p:int) (h:int) (h2:int) (h10:int) (c:int) (hh:int) =
   let h2_4 = h2 / 4 in
   let h2_m = h2 % 4 in
   let h_expand = h10 + (h2_4 * 4 + h2_m) * (n * n) in
   let hh_expand = h10 + (h2_m) * (n * n) + h2_4 * 5 in
   lemma_div_mod h (n * n);
   modulo_addition_lemma hh_expand p h2_4;
   assert (h_expand == hh_expand + h2_4 * (n * n * 4 + (-5)))
   by (int_semiring ())


(* These lemmas go through because of SMT patterns,
   is that the right style to use here?*)

let lemma_shr2_nat (x:nat64) :
  Lemma (shift_right64 x 2 == x / 4) =
  reveal_ishr 64 x 2
let lemma_shr4_nat (x:nat64) :
  Lemma (shift_right64 x 4 == x / 16) =
  reveal_ishr 64 x 4
let lemma_and_mod_n_nat (x:nat64) :
 Lemma (logand64 x 3 == x % 4 /\
        logand64 x 15 == x % 16) =
  reveal_iand 64 x 3;
  reveal_iand 64 x 15
let lemma_and_constants_nat (x:nat64) :
  Lemma (logand64 x 0 == 0 /\
         logand64 x 0xffffffffffffffff == x) =
  reveal_iand 64 x 0;
  reveal_iand 64 x 0xffffffffffffffff

let lemma_clear_lower_2_nat (x:nat64) :
  Lemma (logand64 x 0xfffffffffffffffc == (x/4)*4) =
  reveal_iand 64 x 0xfffffffffffffffc;
  assert (x < pow2_64);
  assert ((x/4)*4 < pow2_64);
  modulo_lemma ((x/4)*4) (pow2_64)

// reveal_iand_all 64 does not work here.
let lemma_poly_constants_nat (x:nat64) :
  Lemma (logand64 x 0x0ffffffc0fffffff < 0x1000000000000000 /\
         logand64 x 0x0ffffffc0ffffffc < 0x1000000000000000 /\
         (logand64 x 0x0ffffffc0ffffffc) % 4 == 0) =
  reveal_iand 64 x 0x0ffffffc0fffffff;
  reveal_iand 64 x 0x0ffffffc0ffffffc

let lemma_and_commutes_nat (x y:nat64) :
  Lemma (logand64 x y == logand64 y x) =
  reveal_iand_all 64;
  lemma_and_commutes x y


// using forall_intro on original bitvector lemmas and
// ireveal_and_all etc. does not solve the goal
let lemma_poly_bits64 () =
    forall_intro (lemma_shr2_nat);
    forall_intro (lemma_shr4_nat);
    forall_intro (lemma_and_mod_n_nat);
    forall_intro (lemma_and_constants_nat);
    forall_intro (lemma_clear_lower_2_nat);
    forall_intro (lemma_poly_constants_nat);
    forall_intro_2 (lemma_and_commutes_nat)

let lemma_mul_strict_upper_bound (x:int) (x_bound:int) (y:int) (y_bound:int) =
  lemma_mult_lt_right y x x_bound;
  if x_bound = 0 || y_bound = 0 then ()
  else
    if y = 0 then
    begin
      assert_norm(x*0 = 0);
      pos_times_pos_is_pos x_bound y_bound
    end
    else
      lemma_mult_lt_left x_bound y y_bound

let lemma_bytes_shift_power2 (y:nat64) =
  lemma_bytes_shift_power2 y;
  reveal_ishl_all 64

#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 1 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 30 --z3refresh"


open FStar.UInt
open FStar.Tactics
open FStar.Tactics.BV

val lemma_bytes_and_mod0: x: uint_t 64 ->
  Lemma (logand #64 x  (0x1 - 1) == x % 0x1)
val lemma_bytes_and_mod1: x: uint_t 64 ->
  Lemma (logand #64 x  (0x100 - 1) == x % 0x100)
val lemma_bytes_and_mod2: x: uint_t 64 ->
  Lemma (logand #64 x  (0x10000 - 1) == x % 0x10000)
val lemma_bytes_and_mod3: x: uint_t 64 ->
  Lemma (logand #64 x  (0x1000000 - 1) == x % 0x1000000)
val lemma_bytes_and_mod4: x: uint_t 64 ->
  Lemma (logand #64 x  (0x100000000 - 1) == x % 0x100000000)
val lemma_bytes_and_mod5: x: uint_t 64 ->
  Lemma (logand #64 x  (0x10000000000 - 1) == x % 0x10000000000)
val lemma_bytes_and_mod6: x: uint_t 64 ->
  Lemma (logand #64 x  (0x1000000000000 - 1) == x % 0x1000000000000)
val lemma_bytes_and_mod7: x: uint_t 64 ->
  Lemma (logand #64 x  (0x100000000000000 - 1) == x % 0x100000000000000)

let lemma_bytes_and_mod0 x =
  assert_by_tactic (logand #64 x (0x1 - 1) == mod #64 x 0x1) bv_tac

let lemma_bytes_and_mod1 x =
  assert_by_tactic (logand #64 x (0x100 - 1) == mod #64 x 0x100) bv_tac

let lemma_bytes_and_mod2 x =
  assert_by_tactic (logand #64 x (0x10000 - 1) == mod #64 x 0x10000) bv_tac
let lemma_bytes_and_mod3 x =
  assert_by_tactic (logand #64 x (0x1000000 - 1) == mod #64 x 0x1000000) bv_tac

let lemma_bytes_and_mod4 x =
  assert_by_tactic (logand #64 x (0x100000000 - 1) == mod #64 x 0x100000000) bv_tac

let lemma_bytes_and_mod5 x =
  assert_by_tactic (logand #64 x (0x10000000000 - 1) == mod #64 x 0x10000000000) bv_tac

let lemma_bytes_and_mod6 x =
  assert_by_tactic (logand #64 x (0x1000000000000 - 1) == mod #64 x 0x1000000000000) bv_tac

let lemma_bytes_and_mod7 x =
  assert_by_tactic (logand #64 x (0x100000000000000 - 1) == mod #64 x 0x100000000000000) bv_tac

let lemma_bytes_and_mod (x:nat64) (y:nat64) =
  reveal_iand_all 64;
  reveal_ishl_all 64;
  match y with
  | 0 ->
      lemma_bytes_shift_constants0 ();
      lemma_bytes_and_mod0 x
  | 1 ->
    lemma_bytes_shift_constants1 ();
    lemma_bytes_and_mod1 x
  | 2 ->
    lemma_bytes_shift_constants2 ();
    lemma_bytes_and_mod2 x
  | 3 ->
    lemma_bytes_shift_constants3 ();
    lemma_bytes_and_mod3 x
  | 4 ->
     lemma_bytes_shift_constants4 ();
     lemma_bytes_and_mod4 x
  | 5 ->
    lemma_bytes_shift_constants5 ();
    lemma_bytes_and_mod5 x
  | 6 ->
    lemma_bytes_shift_constants6 ();
    lemma_bytes_and_mod6 x
  | 7 ->
    lemma_bytes_shift_constants7 ();
lemma_bytes_and_mod7 x

let lemma_mod_factors(x0:nat) (x1:nat) (y:nat) (z:pos) :
  Lemma ((x0 + (y * z) * x1) % z == (x0 % z)) =
  nat_times_nat_is_nat y x1;
  lemma_mod_plus x0 (y*x1) z;
  assert_by_tactic ((y*z)*x1 == (y*x1)*z) canon

let lemma_mul_pos_pos_is_pos_inverse (x:pos) (y:int) :
  Lemma (requires y*x > 0)
        (ensures y > 0) =
  if y = 0 then assert_norm (0*x == 0)
  else if y < 0 then
    begin
      lemma_mult_lt_right x y 0;
      assert_norm (y*x <= 0)
    end
  else ()

#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 8"
let lemma_mod_factor_lo(x0:nat64) (x1:nat64) (y:int) (z:pos) :
  Lemma (requires z < 0x10000000000000000 /\
                  y * z == 0x10000000000000000)
        (ensures ((x0 % z) < pow2_64) /\
                 lowerUpper128_def x0 x1 % z == lowerUpper128_def (x0 % z) 0) =
  lemma_mul_pos_pos_is_pos_inverse z y;
  modulo_range_lemma x0 z;
  lemma_mod_factors x0 x1 y z;
  assert_norm(lowerUpper128_def x0 x1 % z == lowerUpper128_def (x0 % z) 0)

let lemma_mod_power2_lo (x0:nat64) (x1:nat64) (y:int) (z:int) =
    assert (z > 0);
    lemma_mod_factor_lo x0 x1 0x10000000000000000 0x1;
    lemma_mod_factor_lo x0 x1 0x100000000000000 0x100;
    lemma_mod_factor_lo x0 x1 0x1000000000000 0x10000;
    lemma_mod_factor_lo x0 x1 0x10000000000 0x1000000;
    lemma_mod_factor_lo x0 x1 0x100000000 0x100000000;
    lemma_mod_factor_lo x0 x1 0x1000000 0x10000000000;
    lemma_mod_factor_lo x0 x1 0x10000 0x1000000000000;
    lemma_mod_factor_lo x0 x1 0x100 0x100000000000000;
    lemma_bytes_power2 ();
    lowerUpper128_reveal ()

let lemma_power2_add64 (n:nat) =
  pow2_plus 64 n;
  FStar.UInt.pow2_values 64

#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 8"

(* lemma_div_mod <-> lemma_fundamental_div_mod *)
let lemma_part_bound1(a:nat) (b:pos) (c:pos):
  Lemma(0<b*c /\ b*(a/b) % (b*c) <= b * (c-1)) =
    lemma_mul_pos_pos_is_pos b c;
    lemma_div_mod (b*(a/b)) (b*c);
    assert (b*(a/b) % (b*c) = b*(a/b) - (b*c)*((b*(a/b))/(b*c)));
    assert_by_tactic (b*(a/b) - (b*c)*((b*(a/b))/(b*c)) == b*(a/b) - b*(c*((b*(a/b))/(b*c))))
                     canon; // associativity of mul
    distributivity_sub_right b (a/b) (c*((b*(a/b))/(b*c)));
    assert (b*(a/b) - b*(c*((b*(a/b))/(b*c))) == b*((a/b) - (c*((b*(a/b))/(b*c)))));

    lemma_mod_lt (b*(a/b)) (b*c);
    assert (b*(a/b) % (b*c) < b*c);
    assert (b*((a/b) - (c*((b*(a/b))/(b*c)))) < b*c);
    multiplication_order_lemma_int (((a/b) - (c*((b*(a/b))/(b*c))))) c b;
    assert (((a/b) - (c*((b*(a/b))/(b*c)))) < c);
    assert (((a/b) - (c*((b*(a/b))/(b*c)))) <= c-1);
    multiplication_order_eq_lemma_int ((a/b) - (c*((b*(a/b))/(b*c)))) (c-1) b;
    assert (b*((a/b) - (c*((b*(a/b))/(b*c)))) <= b*(c-1));
    assert (b*(a/b) % (b*c) <= b*(c-1))

let lemma_lt_le_trans (a : nat) (b c : pos) :
  Lemma (requires (a < b) /\ b <= c)
        (ensures a < c) = ()

let lemma_part_bound2 (a : nat) (b c: pos) :
    Lemma(0 < b*c /\ (a%b)%(b*c) < b) =
    pos_times_pos_is_pos b c;
    lemma_mod_lt a b; // a%b < b
    assert (0 <= a%b);
    lemma_mul_increases c b; // b <= b * c
    assert (a%b < b);
    lemma_lt_le_trans (a%b) b (b*c);
    assert (a%b < b * c);
    modulo_lemma (a%b) (b*c)

let lemma_truncate_middle (x:nat) (b c:pos) :
  Lemma (0 < b * c /\ (b*x)%(b*c) == b*(x%c)) =
    pos_times_pos_is_pos b c;
    nat_times_nat_is_nat b x; // or x%c
    lemma_div_mod (b*x) (b*c);
    assert (b*x == (b*c)*((b*x)/(b*c)) + (b*x)%(b*c));

    division_multiplication_lemma (b*x) b c;
    assert ((b*c)*((b*x)/(b*c)) + (b*x)%(b*c) == (b*c)*(((b*x)/b)/c) + (b*x)%(b*c));
    swap_mul b x;
    multiple_division_lemma x b;
    assert((b*c)*(((b*x)/b)/c) + (b*x)%(b*c) == (b*c)*(x/c) + (b*x)%(b*c));

    lemma_div_mod x c;
    assert (b*x == b*(c*(x/c) + x%c));
    distributivity_add_right b (c*(x/c)) (b*(x%c));
    paren_mul_right b c (x/c)

let lemma_mod_breakdown (a:nat) (b:pos) (c:pos) :
  Lemma(0<b*c /\ a%(b*c) == b * ((a/b)%c) + a%b) =
  lemma_mul_pos_pos_is_pos b c;
  nat_over_pos_is_nat a b;

  lemma_part_bound1 a b c;
  assert ((b*(a/b)) % (b*c) + (a%b) % (b*c) <= b*(c-1) + (a%b) % (b*c));
  lemma_part_bound2 a b c;
  assert (b*(c-1) + (a%b) % (b*c) <  b*(c-1) + b);
  assert_by_tactic (b*(c-1) + b == b*c) canon;
  assert ((b*(a/b)) % (b*c) + (a%b) % (b*c) < b*c);

  FStar.Math.Lemmas.lemma_div_mod a b;
  assert(a% (b*c) == (b*(a/b) + a%b) % (b*c));
  lemma_mod_lt a b;
  nat_over_pos_is_nat a b;
  nat_times_nat_is_nat b (a/b);
  assert ((b*(a/b)) % (b*c) + (a%b) % (b*c) < b*c);
  modulo_lemma ((b*(a/b)) % (b*c) + (a%b) % (b*c)) (b*c);
  modulo_distributivity (b*(a/b)) (a%b) (b*c); // ((b*(a/b))%(b*c) + (a%b)%(b*c))%(b*c) = ((b*(a/b)) +
                                                                                          //(a%b))%(b*c)
  assert ((b*(a/b) + a%b) % (b*c) == (b*(a/b)) % (b*c) + (a%b) % (b*c));
  lemma_mul_increases c b; // b <= b*c

  swap_mul b (a/b);
  modulo_lemma (a%b) (b*c);
  assert ((a%b) % (b*c) == a%b);
  assert ((b*(a/b)) % (b*c) + (a%b) % (b*c) == (b*(a/b)) % (b*c) + a%b);
  lemma_truncate_middle (a/b) b c


let lemma_mod_hi (x0:nat64) (x1:nat64) (z:nat64) =
  let n = 0x10000000000000000 in
  assert(lowerUpper128_def x0 x1 % lowerUpper128_def 0 z = (x1 * n + x0) % (z * n));
  lemma_mod_breakdown (x1 * n + x0) n z;
  assert ((x1 * n + x0) % (z * n) == n * (((x1 * n + x0) / n) % z) + (x1 * n + x0) % n);
  lemma_mod_plus x0 x1 n;
  assert (n * (((x1 * n + x0) / n) % z) + (x1 * n + x0) % n == n * (((x1 * n + x0) / n) % z) + x0 % n);
  assert(n * (((x1 * n + x0) / n) % z) + x0 % n == n * (x1 % z) + x0);
  lowerUpper128_reveal ()

let lemma_poly_demod (p:pos) (h:int) (x:int) (r:int) =
  distributivity_add_left (h%p) x r; // ((h%p + x)*r)% = ((h%p)*r + x*r)%p
  modulo_distributivity ((h%p)*r) (x*r) p; // ((h%p)*r + x*r)%p = (((h%p)*r)%p + (x*r)%p)%p
  lemma_mod_mul_distr_l h r p; // ((h%p)*r)%p = (h*r)%p ==> ((h*r)%p + (x*r)%p)%p
  lemma_mod_plus_distr_r ((h*r)%p) (x*r) p;
  lemma_mod_plus_distr_l (h*r) (x*r) p

#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 50"
let lemma_reduce128  (h:int) (h2:nat64) (h1:nat64) (h0:nat64) (g:int) (g2:nat64) (g1:nat64) (g0:nat64) =
  reveal_opaque (`%mod2_128) mod2_128;
  lowerUpper128_reveal ();
  lowerUpper192_reveal ();
  reveal_opaque (`%modp) modp;
  assert_norm (mod2_128 (g - 0x400000000000000000000000000000000) == mod2_128 g);
  if (g2<4) then
  begin
    assert(h < 0x3fffffffffffffffffffffffffffffffb);
    assert(h >= 0);
    assert (modp(h) == h % 0x3fffffffffffffffffffffffffffffffb);
    assert (mod2_128(modp(h)) == mod2_128(h));
    lowerUpper128_reveal ();
    assert_norm (mod2_128 h == lowerUpper128_def h0 h1)
  end
  else
  begin
    assert (0 <= h);
    assert (h - 0x3fffffffffffffffffffffffffffffffb <
              0x3fffffffffffffffffffffffffffffffb);

    assert (modp(h) == h % 0x3fffffffffffffffffffffffffffffffb);
    assert (h - 0x3fffffffffffffffffffffffffffffffb == h %
              0x3fffffffffffffffffffffffffffffffb);
    assert (mod2_128(modp(h)) == mod2_128(h - 0x3fffffffffffffffffffffffffffffffb));
    assert(mod2_128(h - 0x3fffffffffffffffffffffffffffffffb) ==
                      mod2_128(g - 0x400000000000000000000000000000000));
    assert(mod2_128(g - 0x400000000000000000000000000000000) == mod2_128(g));
    assert_norm (mod2_128 g == lowerUpper128_def g0 g1)
  end

let lemma_add_key (old_h0:nat64) (old_h1:nat64) (h_in:int) (key_s0:nat64) (key_s1:nat64) (key_s:int) (h0:nat64) (h1:nat64) =
  lowerUpper128_reveal ();
  reveal_opaque (`%mod2_128) mod2_128;
  ()


let lemma_lowerUpper128_and (x:nat128) (x0:nat64) (x1:nat64) (y:nat128) (y0:nat64) (y1:nat64) (z:nat128) (z0:nat64) (z1:nat64) =
  lowerUpper128_reveal ();
  reveal_iand 64 x0 y0;
  reveal_iand 64 x1 y1;
  reveal_iand 128 x y;
  lemma_lowerUpper128_andu x x0 x1 y y0 y1 z z0 z1

let lemma_add_mod128 (x y :int) =
  reveal_opaque (`%mod2_128) mod2_128
