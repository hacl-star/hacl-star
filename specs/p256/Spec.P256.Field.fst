module Spec.P256.Field

open FStar.Mul
open FStar.Tactics
open FStar.Algebra.CommMonoid
open FStar.Tactics.CanonCommSemiring

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

///
/// Finite field of integers modulo the P-256 prime modulus
///
///     p = 2^256 - 2^224 + 2^192 + 2^96 - 1
///

let prime: p:pos{3 < p /\ p < pow2 256} =
  let p = 115792089210356248762697446949407573530086143415290314195533631308867097853951 in
  assert_norm (3 < p /\ p < pow2 256 /\ p = pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1);
  p

/// Field element
let elem = a:nat{a < prime}

[@canon_attr]
let zero: elem = 0

[@canon_attr]
let one: elem = 1

//[@(strict_on_arguments [0;1])]
let ( +% ) (a b:elem) : elem = (a + b) % prime

//[@(strict_on_arguments [0;1])]
let ( *% ) (a b:elem) : elem = (a * b) % prime

//[@(strict_on_arguments [0])]
let ( ~% ) (a:elem) : elem = (-a) % prime

[@canon_attr]
let ( -% ) (a b:elem) : elem = (a +% ~% b)

// See https://github.com/FStarLang/FStar/issues/1923
//[@(strict_on_arguments [0;1])]
val exp: elem -> b:nat -> Tot elem (decreases b)
let rec exp a b =
  if b = 0 then 1
  else
    if b % 2 = 0 then exp (a *% a) (b / 2)
    else a *% exp (a *% a) (b / 2)

// We don't want `pow` to normalize in the proofs below (e.g. `inverse_opp)
// But we want it to normalize for short exponents.
// We define an operator `**` for this second use case.
[@(strict_on_arguments [0;1])]
val pow: elem -> pos -> elem
let rec pow a b =
  if b = 1 then a
  else pow a (b - 1) *% a

[@canon_attr]
val _pow: elem -> pos -> elem
let rec _pow a b =
  if b = 1 then a
  else _pow a (b - 1) *% a

[@canon_attr]
let ( ** ) (a:elem) (k:pos) = _pow a k

/// TODO: `exp` to normalize it efficiently, but it should be reverted to `pow`
//[@(strict_on_arguments [0;1])]
let ( **% ) (a:elem) (k:pos) = exp a k

[@(strict_on_arguments [0])]
let inverse (x:elem{x <> zero}) : elem = x **% (prime - 2)

[@canon_attr]
let ( /% ) (a:elem) (b:elem{b <> zero}) : elem = a *% inverse b

///
/// Field axioms
///

val add_identity (a:elem) : Lemma (zero +% a == a)
let add_identity a = ()

val mul_identity (a:elem) : Lemma (one *% a == a)
let mul_identity a = ()

val add_associative (a b c:elem) : Lemma (a +% b +% c == a +% (b +% c))
let add_associative a b c =
  let open FStar.Math.Lemmas in
  calc (==) {
    a +% b +% c;
    == { }
    ((a + b) % prime + c) % prime;
    == { lemma_mod_plus_distr_l (a + b) c prime }
    ((a + b) + c) % prime;
    == { addition_is_associative a b c }
    (a + (b + c)) % prime;
    == { lemma_mod_plus_distr_r a (b + c) prime }
    a +% (b +% c);
  }

val add_commutative (a b:elem) : Lemma (a +% b == b +% a)
let add_commutative a b = ()

val mul_associative (a b c:elem) : Lemma (a *% b *% c == a *% (b *% c))
let mul_associative a b c =
  let open FStar.Math.Lemmas in
  calc (==) {
    a *% b *% c;
    == { }
    (((a * b) % prime) * c) % prime;
    == { lemma_mod_mul_distr_l (a * b) c prime }
    ((a * b) * c) % prime;
    == { paren_mul_right a b c }
    (a * (b * c)) % prime;
    == { lemma_mod_mul_distr_r a (b * c) prime }
    (a * ((b * c) % prime)) % prime;
    == { }
    a *% (b *% c);
  }

val mul_commutative (a b:elem) : Lemma (a *% b == b *% a)
let mul_commutative a b = ()

[@canon_attr]
let elem_add_cm: cm elem =
  CM zero ( +% ) add_identity add_associative add_commutative

[@canon_attr]
let elem_mul_cm: cm elem =
  CM one ( *% ) mul_identity mul_associative mul_commutative

val mul_add_distr: distribute_left_lemma elem elem_add_cm elem_mul_cm
let mul_add_distr a b c =
  let open FStar.Math.Lemmas in
  calc (==) {
    a *% (b +% c);
    == { }
    (a * (b +% c)) % prime;
    == { lemma_mod_add_distr a (b + c) prime }
    (a * ((b + c) % prime)) % prime;
    == { lemma_mod_mul_distr_r a (b + c) prime }
    (a * (b + c)) % prime;
    == { distributivity_add_right a b c }
    (a * b + a * c) % prime;
    == { lemma_mod_add_distr (a * b) (a * c) prime }
    (a * b + a *% c) % prime;
    == { }
    (a *% c + a * b) % prime;
    == { lemma_mod_add_distr (a *% c) (a * b) prime }
    (a *% c + a *% b) % prime;
    == { }
    (a *% b + a *% c) % prime;
    == { }
    a *% b +% a *% c;
  }

val mul_zero_l: mult_zero_l_lemma elem elem_add_cm elem_mul_cm
let mul_zero_l a = ()

val add_opp (a:elem) : Lemma (a +% ~%a == zero)
let add_opp a = ()

/// See below:
/// val mul_inverse (a:elem{a <> zero}) : Lemma (a *% inverse a == one)

[@canon_attr]
let elem_cr: cr elem = CR elem_add_cm elem_mul_cm ( ~% ) add_opp mul_add_distr mul_zero_l

let p256_field () : Tac unit =
  canon_semiring elem_cr;
  trefl()

let test (a b c:elem) (d:elem{d <> zero}) =
  assert (a**3 == a *% a *% a) by (p256_field ());
  assert (6 *% ~%3 == ~%18) by (p256_field ());
  assert ((a +% b) *% (a +% b) == a *% a +% 2 *% a *% b +% b *% b) by (p256_field ());
  assert ((a +% b) *% (c +% d) == c *% (b +% a) +% a *% d +% b *% d) by (p256_field ());
  assert ((a -% b) *% c == a *% c +% ~%b *% c) by (p256_field ());
  assert (c *% (a /% d) == inverse d *% c *% a) by (p256_field ());
  assert (a *% (b +% c) == (a *% b) +% (a *% c)) by (p256_field ())


///
/// General arithmetic properties
///

val mod_add_distr (a b:int) : Lemma ((a % prime) +% (b % prime) = (a + b) % prime)
let mod_add_distr a b =
  FStar.Math.Lemmas.modulo_distributivity a b prime

val mul_neg_l (a b:elem) : Lemma (~%a *% b == ~%(a *% b))
let mul_neg_l a b =
  assert (~%a *% b == ~%(a *% b)) by (p256_field ())

val mul_neg_r (a b:elem) : Lemma (a *% ~%b == ~%(a *% b))
let mul_neg_r a b =
  assert (a *% ~%b == ~%(a *% b)) by (p256_field ())

val mod_mul_sub_distr_l (a b c:elem) : Lemma (a *% (b -% c) == (a *% b) -% (a *% c))
let mod_mul_sub_distr_l a b c =
  assert (a *% (b -% c) == (a *% b) +% (a *% ~%c)) by (p256_field ());
  mul_neg_r a c

val mod_mul_sub_distr_r (a b c:elem) : Lemma ((b -% c) *% a == (a *% b) -% (a *% c))
let mod_mul_sub_distr_r a b c =
  assert ((b -% c) *% a == (a *% b) -% (a *% c)) by (p256_field ())

val sub_unfold (a b:elem) : Lemma (a -% b == (a - b) % prime)
let sub_unfold a b =
  let open FStar.Math.Lemmas in
  if b = 0 then
    calc (==) {
      a -% b;
      == { }
      (a + (-b) % prime) % prime;
      == { assert_norm (0 % prime == 0) }
      (a + 0 % prime) % prime;
      == { }
      (a - 0) % prime;
    }
  else
    calc (==) {
      a -% b;
      == { }
      (a + (-b) % prime) % prime;
      == { lemma_mod_sub_1 b prime }
      (a + (prime + - b % prime)) % prime;
      == { addition_is_associative a prime (-b % prime) }
      (prime + a - b % prime) % prime;
      == { lemma_mod_plus_distr_l prime (a - b % prime) prime }
      (prime % prime + a - b % prime) % prime;
      == { assert_norm (prime % prime = 0) }
      (a - b % prime) % prime;
      == { lemma_mod_sub_distr a b prime }
      (a - b) % prime;
    }

val mod_sub_distr (a b:int) : Lemma ((a % prime) -% (b % prime) = (a - b) % prime)
let mod_sub_distr a b =
  let open FStar.Math.Lemmas in
  calc (==) {
    a % prime -% b % prime;
    == { sub_unfold (a % prime) (b % prime) }
    (a % prime - b % prime) % prime;
    == { lemma_mod_sub_distr (a % prime) b prime }
    (a % prime - b) % prime;
    == { lemma_mod_plus_distr_l a (-b) prime }
    (a - b) % prime;
  }

val mod_mul_distr (a b:int) : Lemma ((a % prime) *% (b % prime) = (a * b) % prime)
let mod_mul_distr a b =
  let open FStar.Math.Lemmas in
  calc (==) {
    a * b % prime;
    == { lemma_mod_mul_distr_l a b prime }
    (a % prime) * b % prime;
    == { lemma_mod_mul_distr_r (a % prime) b prime }
    (a % prime) * (b % prime) % prime;
    == { }
    (a % prime) *% (b % prime);
  }

val sub_mod (n:pos) (a b:int) : Lemma
  (requires (a - b) % n = 0)
  (ensures  a % n = b % n)
let sub_mod n a b =
  FStar.Math.Lemmas.mod_add_both (a - b) 0 b n

val mod_sub (n:pos) (a b:int) : Lemma
  (requires a % n = b % n)
  (ensures  (a - b) % n = 0)
let mod_sub n a b =
  FStar.Math.Lemmas.mod_add_both a b (-b) n

val mul_coprime_eq (a b c r s:elem) : Lemma
  (requires a *% c == b *% c /\ r * prime + s * c = 1)
  (ensures  a == b)
let mul_coprime_eq a b c r s =
  let open FStar.Math.Lemmas in
  mod_sub prime (a * c) (b * c);
  lemma_mul_sub_distr c a b;
  assert (c * (a - b) % prime = 0);
  FStar.Math.Euclid.euclid prime c (a - b) r s;
  assert ((a - b) % prime = 0);
  sub_mod prime a b;
  assert (a % prime == b % prime);
  small_mod a prime;
  small_mod b prime

val mod_neg_eq (a:elem) : Lemma
  (requires a % prime = (-a) % prime)
  (ensures  a = 0)
let mod_neg_eq a =
  let open FStar.Math.Lemmas in
  if a = 0 then ()
  else
    begin
    mod_add_both a (-a) a prime;
    assert ((a + a) % prime == (-a + a) % prime);
    if a + a < prime then ()
    else
      begin
      assert (a + a - prime < prime);
      lemma_mod_sub_1 a prime;
      assert ((a + a - prime) % prime == 0 % prime);
      lemma_mod_injective prime (a + a - prime) 0;
      assert (a + a = prime);
      assert (2 * a = prime);
      assert_norm (prime % 2 = 1)
      end
    end

val mod_sub_congr (a b c d x:int) : Lemma
  (requires (a - c) % prime = (b - d) % prime)
  (ensures  (a - x - b) % prime = (c - x - d) % prime)
let mod_sub_congr a b c d x =
  FStar.Math.Lemmas.mod_add_both (a - c) (b - d) c prime;
  assert (a % prime = ((b - d + c) % prime));
  FStar.Math.Lemmas.mod_add_both a (b - d + c) (-x) prime;
  assert ((a - x) % prime = ((b - d + c - x) % prime));
  FStar.Math.Lemmas.mod_add_both (a - x) (b - d + c - x) (-b) prime;
  assert ((a - x - b) % prime = ((c - x - d) % prime))

/// Axiomatizing the divisors of the prime modulus
/// We could alternatively verify a primality certificate
assume
val divides_prime : unit -> Lemma (FStar.Math.Euclid.is_prime prime)

val mod_mult_congr_aux (a b c:elem) : Lemma
  (requires (a *% c) = (b *% c) /\ b < a /\ c <> 0)
  (ensures  a = b)
let mod_mult_congr_aux a b c =
  let open FStar.Math.Lemmas in
  calc (==>) {
    (a *% c) == (b *% c);
    ==> { mod_add_both (a * c) (b * c) (-b * c) prime }
    (a * c - b * c) % prime == (b * c - b * c) % prime;
    ==> { swap_mul a c; swap_mul b c; lemma_mul_sub_distr c a b }
    (c * (a - b)) % prime == (b * c - b * c) % prime;
    ==> { small_mod 0 prime }
    (c * (a - b)) % prime == 0;
  };
  divides_prime ();
  let r, s = FStar.Math.Euclid.bezout_prime prime c in
  FStar.Math.Euclid.euclid prime c (a - b) r s

val mod_mult_congr (a b c:elem) : Lemma
  (requires (a *% c) = (b *% c) /\ c <> 0)
  (ensures  a = b)
let mod_mult_congr a b c =
  if a = b then ()
  else if b < a then mod_mult_congr_aux a b c
  else mod_mult_congr_aux b a c

val opp_opp (a:elem) : Lemma (~%(~%a) == a)
let opp_opp a =
  assert ((~%(~%a) == a)) by (p256_field ())

val mul_opp_cancel (a b:elem) : Lemma (~%a *% ~%b == a *% b)
let mul_opp_cancel a b =
  assert (~%a *% ~%b == a *% b) by (p256_field ())

///
/// `pow` and `exp`
///

#push-options "--fuel 1"

val pow_one (k:pos) : Lemma (pow one k == one)
let rec pow_one = function
  | 1 -> ()
  | k -> pow_one (k-1)

val pow_plus (a:elem) (k m:pos): Lemma
  (ensures pow a (k + m) == pow a k *% pow a m)
  (decreases k)
let rec pow_plus a k m =
  match k with
  | 1 -> ()
  | _ ->
    calc (==) {
      pow a (k + m);
      == { }
      pow a ((k + m) - 1) *% a;
      == { pow_plus a (k - 1) m }
      (pow a (k - 1) *% pow a m) *% a;
      == { mul_associative a (pow a (k - 1)) (pow a m) }
      pow a k *% pow a m;
    }

val pow_mul_reorder (a b c d:elem) : Lemma
  ((a *% b) *% (c *% d) == (a *% c) *% (b *% d))
let pow_mul_reorder a b c d =
  assert (((a *% b) *% (c *% d) == (a *% c) *% (b *% d))) by (p256_field ())

val pow_mul (a b:elem) (k:pos) : Lemma (pow (a *% b) k == pow a k *% pow b k)
let rec pow_mul a b k =
  match k with
  | 1 -> ()
  | _ ->
    calc (==) {
      pow (a *% b) k;
      == { }
      (a *% b) *% pow (a *% b) (k - 1);
      == { pow_mul a b (k - 1) }
      (a *% b) *% (pow a (k - 1) *% pow b (k - 1));
      == { pow_mul_reorder a b (pow a (k - 1)) (pow b (k - 1)) }
      pow a k *% pow b k;
    }

val pow_exp (a:elem) (k:pos) : Lemma
  (ensures exp a k == pow a k)
  (decreases k)
let rec pow_exp a k =
  if k = 1 then assert_norm (exp a 1 == a)
  else
    if k % 2 = 0 then
      begin
      calc (==) {
        exp a k;
        == { }
        exp (a *% a) (k / 2);
        == { pow_exp (a *% a) (k / 2) }
        pow (a *% a) (k / 2);
        == { pow_mul a a (k / 2) }
        pow a (k / 2) *% pow a (k / 2);
        == { pow_plus a (k / 2) (k / 2) }
        pow a k;
      }
      end
    else // k % 2 = 1
      begin
      calc (==) {
        exp a k;
        == { }
        a *% exp (a *% a) (k / 2);
        == { pow_exp (a *% a) (k / 2) }
        a *% pow (a *% a) (k / 2);
        == { pow_mul a a (k / 2) }
        a *% (pow a (k / 2) *% pow a (k / 2));
        == { pow_plus a (k / 2) (k / 2); mul_commutative a (pow a (k - 1)) }
        pow a k;
      }
      end

#pop-options

#push-options "--fuel 2"

val pow_even (a:elem) (k:pos{k % 2 = 0}) : Lemma (pow (~%a) k == pow a k)
let rec pow_even a k =
  if k = 2 then mul_opp_cancel a a
  else
    calc (==) {
      pow (~%a) k;
      == { }
      (pow (~%a) (k - 2) *% (~%a)) *% (~%a);
      == { mul_associative (pow (~%a) (k - 2)) (~%a) (~%a) }
      pow (~%a) (k - 2) *% (~%a *% ~%a);
      == { pow_even a (k - 2) }
      pow a (k - 2) *% (~%a *% ~%a);
      == { mul_neg_r (~%a) a }
      pow a (k - 2) *% (~%(~%a *% a));
      == { mul_commutative (~%a) a; mul_neg_r a a }
      pow a (k - 2) *% (~%(~%(a *% a)));
      == { opp_opp (a *% a) }
      pow a (k - 2) *% (a *% a);
      == { mul_associative (pow a (k - 2)) a a }
      pow a k;
    }

val pow_odd (a:elem) (k:pos{k % 2 = 1}) : Lemma (pow (~%a) k == ~%(pow a k))
let rec pow_odd a k =
  if k = 1 then ()
  else
    calc (==) {
      pow (~%a) k;
      == { }
      (pow (~%a) (k - 2) *% (~%a)) *% (~%a);
      == { mul_associative (pow (~%a) (k - 2)) (~%a) (~%a) }
      pow (~%a) (k - 2) *% (~%a *% ~%a);
      == { pow_odd a (k - 2) }
      ~%(pow a (k - 2)) *% (~%a *% ~%a);
      == { mul_neg_r (~%a) a }
      ~%(pow a (k - 2)) *% (~%(~%a *% a));
      == { mul_commutative (~%a) a; mul_neg_r a a }
      ~%(pow a (k - 2)) *% (~%(~%(a *% a)));
      == { opp_opp (a *% a) }
      ~%(pow a (k - 2)) *% (a *% a);
      == { mul_neg_l (pow a (k - 2)) (a *% a) }
      ~%(pow a (k - 2) *% (a *% a));
      == { mul_associative (pow a (k - 2)) a a }
      ~%(pow a k);
    }

#pop-options

val inverse_opp (a:elem{a <> zero}) : Lemma (inverse (~%a) == ~%(inverse a))
let inverse_opp a =
  calc (==) {
    inverse (~%a);
    == { pow_exp (~%a) (prime - 2) }
    pow (~%a) (prime - 2);
    == { pow_odd a (prime - 2) }
    ~%(pow a (prime - 2));
    == { pow_exp a (prime - 2) }
    ~%(inverse a);
  }

/// Fermat's Little Theorem
///
/// The easiest is to prove it by induction from the Freshman's dream identity
///
///   pow (a +% b) prime = pow a prime +% pow b prime
///
/// which follows from the Binomial Theorem
///
///   pow (a + b) n = sum_{i=0}^n (binomial n k * pow a (n - i) * pow b i)
///
/// which in turn can be proved by induction from Pascal's identity
///
///   binomial n k + binomial n (k - 1) = binomial (n + 1) k

assume
val fermat (a:elem) : Lemma (pow a (prime - 1) == one)

#push-options "--fuel 1"

val mul_inverse (a:elem{a <> zero}) : Lemma (a *% inverse a == one)
let mul_inverse a =
  let open FStar.Math.Lemmas in
  calc (==) {
    a *% (a *% inverse a);
    == { pow_exp a (prime - 2) }
    a *% (a *% pow a (prime - 2));
    == { }
    a *% pow a (prime - 1);
    == { fermat a }
    a *% one;
    == { mul_commutative a one; mul_identity a }
    a;
  };
  mod_mult_congr (a *% inverse a) one a

#pop-options

val mul_one_r (a:elem) : Lemma (a *% one == a)
let mul_one_r a =
  mul_commutative a one; mul_identity a

val opp_sub (a b:elem) : Lemma (~%(a -% b) == b -% a)
let opp_sub a b =
  assert (~%(a -% b) == b -% a) by (p256_field ())

val sub_zero (a:elem) : Lemma (a -% zero == a)
let sub_zero a =
  assert_norm (~%zero == zero);
  add_commutative a zero;
  add_identity a

val sub_neq (a b:elem) : Lemma (requires a <> b) (ensures a -% b <> 0)
let sub_neq a b = ()

val sub_congr (a b c:elem) : Lemma
  (a == b <==> a -% c == b -% c)
let sub_congr a b c = ()

val add_congr (a b c:elem) : Lemma
  (a == b <==> a +% c == b +% c)
let add_congr a b c = ()

val add_sub_congr (a b c d:elem) : Lemma
  (a +% b == c +% d <==> a -% c == d -% b)
let add_sub_congr a b c d =
  calc (<==>) {
    a +% b == c +% d;
    <==> { sub_congr (a +% b) (c +% d) b }
    a +% b -% b == c +% d -% b;
    <==> { add_associative a b (~%b); add_opp b }
    a == c +% d -% b;
    <==> { sub_congr a (c +% d -% b) c}
    a -% c == c +% d -% b -% c;
    <==> { assert (c +% d -% b -% c == (c -% c) +% (d -% b)) by (p256_field ()) }
    a -% c == (c -% c) +% (d -% b);
    == { add_opp c; add_identity (d -% b) }
    a -% c == d -% b;
  }

val opp_add (a b:elem) : Lemma (~%(a +% b) == ~%a +% ~%b)
let opp_add a b =
  assert (~%(a +% b) == ~%a +% ~%b) by (p256_field ())

val mult_eq_zero (a b:elem) : Lemma (a *% b == 0 <==> (a == 0 \/ b == 0))
let mult_eq_zero a b =
  if a = 0 || b = 0 then ()
  else if (a *% b) = 0 then mod_mult_congr a 0 b

val inverse_mul (a b:elem) : Lemma
  (requires a <> 0 /\ b <> 0)
  (ensures  a *% b <> 0 /\ inverse a *% inverse b == inverse (a *% b))
let inverse_mul a b =
  mult_eq_zero a b;
  calc (==) {
    inverse a *% inverse b;
    == { pow_exp a (prime - 2); pow_exp b (prime - 2) }
    pow a (prime - 2) *% pow b (prime - 2);
    == { pow_mul a b (prime - 2) }
    pow (a *% b) (prime - 2);
    == { pow_exp (a *% b) (prime - 2) }
    inverse (a *% b);
  }

val mul_opp_1 (a:elem) : Lemma (~%1 *% a == ~%a)
let mul_opp_1 a =
  assert (~%1 *% a == ~%a) by (p256_field ())

val sub_mul_l (a b c:elem) : Lemma (a -% b *% c == a +% ~%b *% c)
let sub_mul_l a b c =
  assert (a -% b *% c == a +% ~%b *% c) by (p256_field ())

val square_binom (a b:elem) : Lemma
  ((a +% b) *% (a +% b) == a *% a +% b *% b +% 2 *% a *% b)
let square_binom a b =
  assert (((a +% b) *% (a +% b) == a *% a +% b *% b +% 2 *% a *% b)) by (p256_field ())

val div_plus_l (a b c:elem) : Lemma
  (requires b <> 0)
  (ensures  a /% b +% c == (a +% b *% c) /% b)
let div_plus_l a b c =
  assert ((a +% b *% c) /% b == a /% b +% (b /% b) *% c) by (p256_field ());
  mul_inverse b

val div_mul_eq_l (a b c:elem) : Lemma
  (requires b <> 0 /\ c <> 0)
  (ensures  (mult_eq_zero c b; a /% b == (c *% a) /% (c *% b)))
let div_mul_eq_l a b c =
  mult_eq_zero c b;
  calc (==) {
    a /% b;
    == { mul_identity (a *% b) }
    one *% (a /% b);
    == { mul_inverse c }
    (c /% c) *% (a /% b);
    == { pow_mul_reorder c (inverse c) a (inverse b) }
    (c *% a) *% (inverse c *% inverse b);
    == { inverse_mul c b }
    (c *% a) /% (c *% b);
  }

val div_eq (a b c d:elem) : Lemma
  (requires b <> 0 /\ d <> 0 /\ a *% d == c *% b)
  (ensures  a /% b == c /% d)
let div_eq a b c d =
  mult_eq_zero d b;
  calc (==) {
    a /% b;
    == { div_mul_eq_l a b d }
    (d *% a) /% (d *% b);
    == { inverse_mul d b; mul_commutative d a }
    (c *% b) *% (inverse d *% inverse b);
    == { assert ((c *% b) *% (inverse d *% inverse b) ==
                (c *% inverse d) *% (b *% inverse b))
         by (p256_field()) }
    (c *% inverse d) *% (b *% inverse b);
    == { mul_inverse b; mul_one_r (c *% inverse d) }
    c /% d;
  }

#push-options "--fuel 1"

val pow_eq_zero (a:elem) (k:pos) : Lemma (a**k == 0 <==> a == 0)
let rec pow_eq_zero a k =
  match k with
  | 1 -> ()
  | _ ->
    begin
    mult_eq_zero a (_pow a (k - 1));
    pow_eq_zero a (k - 1)
    end

val pow_inverse (a:elem{a <> 0}) (k:pos) : Lemma
  (pow_eq_zero a k; (inverse a)**k == inverse (a**k))
let rec pow_inverse a k =
  match k with
  | 1 -> ()
  | _ ->
    begin
    pow_eq_zero a (k-1);
    inverse_mul a (_pow a (k - 1));
    pow_inverse a (k - 1)
    end

#pop-options
