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