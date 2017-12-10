module Spec.RSA.Lemmas

open FStar.Mul
open FStar.Math.Lemmas

type elem (n:nat) = e:nat{e < n}

(* LEMMAS *)
#reset-options "--z3rlimit 30 --max_fuel 2"
val pow : x:nat -> n:nat -> Tot nat
let rec pow x n =
  match n with
  | 0 -> 1
  | n -> x * pow x (n - 1)

val lemma_pow: x:nat -> n:nat -> m:nat -> Lemma
  (pow x n * pow x m = pow x (n + m))
let rec lemma_pow x n m =
  let ass (x y z : nat) : Lemma ((x*y)*z == x*(y*z)) = () in
  match n with
  | 0 -> ()
  | _ -> lemma_pow x (n-1) m; ass x (pow x (n-1)) (pow x m)

val lemma_pow2_greater_1: x:nat{x > 1} -> Lemma
	(requires True)
	(ensures (pow2 (x - 1) > 1))
	[SMTPat (pow2 (x - 1))]
let rec lemma_pow2_greater_1 x =
	match x with
	| 2 -> ()
	| _ -> lemma_pow2_greater_1 (x - 1)

val lemma_pow_0: b:nat{b > 0} -> Lemma (pow 0 b = 0)
let rec lemma_pow_0 b =
	match b with
	| 1 -> ()
	| _ -> lemma_pow_0 (b - 1)

val lemma_pow_1: b:nat -> Lemma (pow 1 b = 1)
let rec lemma_pow_1 b =
	match b with
	|  0 -> ()
	| _ -> lemma_pow_1 (b - 1)

#reset-options "--z3rlimit 30 --max_fuel 0"

val lemma_pow_pow:
	a:nat -> b:nat -> c:nat -> Lemma (pow a (b * c) = pow (pow a b) c)
let lemma_pow_pow a b c = admit()

val lemma_pow_a2_b:
	a:nat -> b:nat -> Lemma (pow (a * a) b = pow a (2 * b))
let lemma_pow_a2_b a b = admit()

val lemma_pow_mod:
	a:nat -> b:nat -> n:pos -> Lemma ((pow a b) % n == (pow (a % n) b) % n)
let lemma_pow_mod a b n = admit()

val lemma_div_mod:
	a:nat -> p:pos -> Lemma (a = p * (a / p) + a % p)
let lemma_div_mod a p = ()

val lemma_mult_3:
	a:nat -> b:nat -> c:nat -> Lemma (a * b * c = c * a * b)
let lemma_mult_3 a b c = ()

(* LEMMAS for exponent blinding *)
val lemma_mod_pq:
	a:nat -> b:nat -> p:nat{p > 1} -> q:nat{q > 1} -> Lemma
	(requires (a % p = b /\ a % q = b))
	(ensures (a % (p * q) = b))
let lemma_mod_pq a b p q = admit()

// m ^ (p - 1) = 1 (mod p) where m is any integer and p is a prime number
val fermat_little_theorem:
	p:nat{p > 1} -> m:nat -> Lemma ((pow m (p - 1)) % p = 1)
let fermat_little_theorem p m = admit()

#reset-options "--z3rlimit 100 --max_fuel 0"

val lemma_exp_blinding_1:
	n:nat{n > 1} -> phi_n:nat -> p:elem n{p > 1} ->
	q:elem n{q > 1} -> m:elem n -> Lemma
	(requires (phi_n == (p - 1) * (q - 1) /\ n = p * q))
	(ensures ((pow m phi_n) % q == 1))
let lemma_exp_blinding_1 n phi_n p q m =
	lemma_pow_pow m (q - 1) (p - 1);
	lemma_pow_mod (pow m (q - 1)) (p - 1) q;
	fermat_little_theorem q m;
	lemma_pow_1 (p - 1);
	assert ((pow m phi_n) % q == 1)

#reset-options "--z3rlimit 300 --max_fuel 0"

val lemma_exp_blinding:
	n:nat{n > 1} -> phi_n:nat -> p:elem n{p > 1} -> q:elem n{q > 1} ->
	d:elem n{d > 0} -> m:elem n -> r:nat -> Lemma
	(requires (phi_n == (p - 1) * (q - 1) /\ n = p * q))
	(ensures ((pow m (d + r * phi_n)) % n  == (pow m d) % n))
let lemma_exp_blinding n phi_n p q d m r =
	let res = (pow m (d + r * phi_n)) % n in
	lemma_pow m d (r * phi_n);
	assert (pow m (d + r * phi_n) == pow m d * pow m (r * phi_n));
	lemma_pow_pow m phi_n r;
	assert (pow m (phi_n * r) == pow (pow m phi_n) r);
	lemma_pow_mod (pow m phi_n) r n;
	assert ((pow (pow m phi_n) r) % n == (pow ((pow m phi_n) % n) r) % n);

	lemma_exp_blinding_1 n phi_n p q m;
	assert ((pow m phi_n) % q == 1);
	lemma_exp_blinding_1 n phi_n q p m;
	assert ((pow m phi_n) % p == 1);
	lemma_mod_pq (pow m phi_n) 1 p q;
	assert ((pow m phi_n) % n = 1);

	lemma_pow_1 r;
	modulo_lemma 1 n;
	assert ((pow 1 r) % n = 1);
	assert ((pow m (r * phi_n)) % n = 1);
	lemma_mod_mul_distr_l (pow m (r * phi_n)) (pow m d) n;
	assert (res == (((pow m (r * phi_n)) % n) * pow m d) % n);
    assert ((pow m (d + r * phi_n)) % n  == (pow m d) % n)

(* LEMMAS for modular exponentiation *)
val lemma_mod_exp:
	n:nat{n > 1} -> a:nat -> a2:nat ->
	b:nat -> b2:nat -> acc:elem n -> res:nat -> Lemma
	(requires (a2 == (a * a) % n /\ b2 == b / 2 /\ res == (pow a2 b2 * acc) % n))
	(ensures (res == (pow a (2 * b2) * acc) % n))

let lemma_mod_exp n a a2 b b2 acc res =
	let res = (pow a2 b2 * acc) % n in
	lemma_mod_mul_distr_l (pow a2 b2) acc n;
	assert (((pow a2 b2) * acc) % n == ((pow a2 b2) % n * acc) % n);
	lemma_pow_mod (a * a) b2 n;
	assert ((pow a2 b2) % n == (pow (a * a) b2) % n);
	lemma_pow_a2_b a b2;
	assert ((pow (a * a) b2) % n == (pow a (2 * b2)) % n);
	assert (res == ((pow a (2 * b2)) % n * acc) % n);
	lemma_mod_mul_distr_l (pow a (2 * b2)) acc n

(* LEMMAS for Karatsuba's multiplication *)
val lemma_distributivity_mult: a:int -> b:int -> c:int -> d:int -> Lemma
  ((a + b) * (c + d) = a * c + a * d + b * c + b * d)
let lemma_distributivity_mult a b c d = ()

#reset-options "--z3rlimit 300 --initial_fuel 0 --max_fuel 0"

val lemma_karatsuba_mult:
	x:nat -> a:nat -> a0:nat -> a1:nat ->
	b:nat -> b0:nat -> b1:nat -> Lemma
	(requires (let pow_x = pow2 (pow2 x) in
		      a == a1 * pow_x + a0 /\ b == b1 * pow_x + b0))
	(ensures (let pow_x = pow2 (pow2 x) in
		      let pow_x1 = pow2 (pow2 (x + 1)) in
		      a * b == a1 * b1 * pow_x1 + (a0 * b1 + a1 * b0) * pow_x + a0 * b0))

let lemma_karatsuba_mult x a a0 a1 b b0 b1 =
	let pow_x = pow2 (pow2 x) in
	let pow_x1 = pow2 (pow2 (x + 1)) in
	assert (a * b == (a1 * pow_x + a0) * (b1 * pow_x + b0));
	lemma_distributivity_mult (a1 * pow_x) a0 (b1 * pow_x) b0;
	assert (a * b == a1 * b1 * pow_x * pow_x + (a0 * b1 + a1 * b0) * pow_x + a0 * b0);
	pow2_plus (pow2 x) (pow2 x);
	assert (pow2 (pow2 x) * pow2 (pow2 x) == pow2 (pow2 x + pow2 x));
	pow2_double_sum x;
	assert (pow2 x + pow2 x == pow2 (x + 1))

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

val lemma_pow_div_karatsuba:
	x0:nat{x0 > 0} -> b:nat{b < pow2 (pow2 x0)} -> Lemma
	(requires (True))
	(ensures (let pow_x = pow2 (pow2 (x0 - 1)) in
		      let b1 = b / pow_x in
	 	      0 <= b1 /\ b1 < pow_x))

let lemma_pow_div_karatsuba x0 b =
	let x = x0 - 1 in
	let pow_x = pow2 (pow2 x) in
	pow2_lt_compat x0 x;
	lemma_div_lt b (pow2 x0) (pow2 x);
	assert (b / pow_x < pow2 (pow2 x0 - pow2 x));
	pow2_plus (x0 - 1) 1;
	assert_norm (pow2 1 = 2);
	assert (pow2 x0 - pow2 (x0 - 1) == (pow2 (x0 - 1)) * (2 - 1))

val abs: x:int -> Tot (y:int{ (x >= 0 ==> y = x) /\ (x < 0 ==> y = -x) })
let abs x = if x >= 0 then x else -x

(* LEMMAS for Montgomery's arithmetic *)
#reset-options "--max_fuel 0"

val lemma_div_lt_ab: a:nat -> b:nat -> d:pos -> Lemma
    (requires (a < b))
    (ensures (a / d < b / d))
let lemma_div_lt_ab a b d = admit()

val lemma_mod_div_simplify: a:nat -> r:nat{r > 0} -> n:nat{n > 0} -> Lemma
  (((a * ((r * r) % n)) / r) % n == (a * r) % n)
let lemma_mod_div_simplify a r n = admit()

val lemma_mont_reduction:
	res:nat -> r:nat{r > 0} -> c:nat -> n:nat{n > 0} -> m:nat -> Lemma
	(requires (res = (c + m * n) / r))
	(ensures (res % n == (c / r) % n))
let lemma_mont_reduction res r c n m = admit()