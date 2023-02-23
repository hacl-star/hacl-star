module Spec.P256.Lemmas

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Tactics
open FStar.Tactics.Canon

open Lib.IntTypes

open Spec.P256.Constants

#set-options " --z3rlimit 100"

val pow: a:nat -> b:nat -> nat
let rec pow a b =
  if b = 0 then 1
  else a * (pow a (b - 1))


val modulo_distributivity_mult: a: int -> b: int -> c: pos ->
  Lemma ((a * b) % c = ((a % c) * (b % c)) % c)

let modulo_distributivity_mult a b c =
  lemma_mod_mul_distr_l a b c;
  lemma_mod_mul_distr_r (a % c) b c


val power_one: a: nat -> Lemma (pow 1 a == 1)
let rec power_one a =
  match a with
  | 0 -> assert_norm (pow 1 0 == 1)
  | _ -> power_one (a - 1)



val pow_plus: a: nat -> b: nat -> c: nat ->
  Lemma (ensures (pow a b * pow a c = pow a (b + c)))
  (decreases b)

let rec pow_plus a b c =
  match b with
  | 0 -> assert_norm (pow a 0 = 1)
  | _ -> pow_plus a (b - 1) c



val power_distributivity: a: nat -> b: nat -> c: pos -> Lemma ((pow (a % c) b) % c = (pow a b) % c)
let rec power_distributivity a b c =
   match b with
   | 0 -> ()
   | _ ->
     power_distributivity a (b - 1) c;
     modulo_distributivity_mult (pow a (b -1)) a c;
     lemma_mod_twice a c;
     modulo_distributivity_mult (pow (a % c) (b -1)) (a % c) c


val power_distributivity_2: a: nat -> b: nat -> c: pos -> Lemma (pow (a * b) c == pow a c * pow b c)
let rec power_distributivity_2 a b c =
  match c with
  |0 -> ()
  |1 -> ()
  | _ ->
    power_distributivity_2 a b (c - 1);
    assert_by_tactic (pow a (c - 1) * pow b (c - 1) * a * b == (pow a c * pow b c)) canon


val power_mult: a: nat -> b: nat -> c: nat -> Lemma (pow (pow a b) c == pow a (b * c))
let rec power_mult a b c =
  match c with
  |0 -> ()
  |_ ->  power_mult a b (c - 1);
    pow_plus a (b * (c - 1)) b



type elem (n:pos) = x:nat{x < n}

let fmul (#n:pos) (x:elem n) (y:elem n) : elem n = (x * y) % n

val exp: #n: pos -> a: elem n -> b: pos -> Tot (elem n) (decreases b)
let rec exp #n a b =
  if b = 1 then a
  else
    if b % 2 = 0 then exp (fmul a a) (b / 2)
    else fmul a (exp (fmul a a) (b / 2))


let modp_inv_prime (prime: pos {prime > 3}) (x: elem prime) : Tot (elem prime) =
  (exp #prime x (prime - 2)) % prime


let modp_inv2_prime (x: int) (p: nat {p > 3}) : Tot (elem p) = modp_inv_prime p (x % p)


let modp_inv2 (x: nat) : Tot (elem prime256) =
  assert_norm(prime256 > 3);
  modp_inv2_prime x prime256


let min_one_prime (prime: pos {prime > 3}) (x: int) : Tot (elem prime) =
  let p = x % prime in
  exp #prime p (prime - 1)



(* Start of Marina RSA PSS code *)
// local
val lemma_fpow_unfold0: a: nat -> b: pos {1 < b /\ b % 2 = 0} -> prime: pos { a < prime} -> Lemma (
  exp #prime a b = exp #prime (fmul a a) (b / 2))
let lemma_fpow_unfold0 a b prime = ()


// local
val lemma_fpow_unfold1: a: nat -> b: pos {1 < b /\ b % 2 = 1} -> prime: pos { a < prime} -> Lemma (
  exp #prime a b = fmul (exp #prime (fmul a a) (b / 2)) a)
let lemma_fpow_unfold1 a b prime = ()


// local
val lemma_pow_unfold: a: nat -> b: pos -> Lemma (a * pow a (b - 1) == pow a b)
let lemma_pow_unfold a b = ()


val lemma_mul_associativity_3: a: nat -> b: nat -> c: nat -> Lemma (a * b * c == a * c * b)
let lemma_mul_associativity_3 a b c = ()


// local
val lemma_pow_double: a: nat -> b: nat -> Lemma (pow (a * a) b == pow a (b + b))
let rec lemma_pow_double a b =
  if b = 0 then ()
  else begin
    calc (==) {
      pow (a * a) b;
      (==) { lemma_pow_unfold (a * a) b }
      a * a * pow (a * a) (b - 1);
      (==) { lemma_pow_double a (b - 1) }
      a * a * pow a (b + b - 2);
      (==) {power_one  a }
      pow a 1 * pow a 1 * pow a (b + b - 2);
      (==) { pow_plus a 1 1 }
      pow a 2 * pow a (b + b - 2);
      (==) { pow_plus a 2 (b + b - 2) }
      pow a (b + b);
    };
    assert (pow (a * a) b == pow a (b + b))
  end


val lemma_pow_mod_n_is_fpow: n:pos -> a:nat{a < n} -> b:pos -> Lemma
  (ensures (exp #n a b == pow a b % n)) (decreases b)

let rec lemma_pow_mod_n_is_fpow n a b =
  if b = 1 then ()
  else begin
    if b % 2 = 0 then begin
      calc (==) {
	exp #n a b;
	(==) { lemma_fpow_unfold0 a b n}
	exp #n (fmul #n a a) (b / 2);
	(==) { lemma_pow_mod_n_is_fpow n (fmul #n a a) (b / 2) }
	pow (fmul #n a a) (b / 2) % n;
	(==) { power_distributivity (a * a) (b / 2) n }
	pow (a * a) (b / 2) % n;
	(==) { lemma_pow_double a (b / 2) }
	pow a b % n;
      };
      assert (exp #n a b == pow a b % n) end
    else begin
      calc (==) {
	exp #n a b;
	(==) { lemma_fpow_unfold1 a b n }
	fmul a (exp (fmul #n a a) (b / 2));
	(==) { lemma_pow_mod_n_is_fpow n (fmul #n a a) (b / 2) }
	fmul a (pow (fmul #n a a) (b / 2) % n);
	(==) { power_distributivity (a * a) (b / 2) n }
	fmul a (pow (a * a) (b / 2) % n);
	(==) { lemma_pow_double a (b / 2) }
	fmul a (pow a (b / 2 * 2) % n);
	(==) { Math.Lemmas.lemma_mod_mul_distr_r a (pow a (b / 2 * 2)) n }
	a * pow a (b / 2 * 2) % n;
	(==) { power_one a }
	pow a 1 * pow a (b / 2 * 2) % n;
	(==) { power_distributivity_2 a 1 (b / 2 * 2) }
	pow a (b / 2 * 2 + 1) % n;
	(==) { Math.Lemmas.euclidean_division_definition b 2 }
	pow a b % n;
      };
      assert (exp #n a b == pow a b % n) end
  end

(* End of Marina RSA PSS code *)


val modulo_distributivity_mult_last_two: a: int -> b: int -> c: int -> d: int -> e: int -> f: pos -> Lemma (
  (a * b * c * d * e) % f = (a * b * c * ((d * e) % f)) % f)

let modulo_distributivity_mult_last_two a b c d e f =
  assert_by_tactic (a * b * c * d * e == a * b * c * (d * e)) canon;
  lemma_mod_mul_distr_r (a * b * c) (d * e) f


val lemma_multiplication_to_same_number: a: nat -> b: nat ->c: nat -> prime: pos ->
  Lemma
    (requires (a % prime = b % prime))
    (ensures ((a * c) % prime = (b * c) % prime))

let lemma_multiplication_to_same_number a b c prime =
  lemma_mod_mul_distr_l a c prime;
  lemma_mod_mul_distr_l b c prime


val lemma_division_is_multiplication:
  t3: nat{ exists (k: nat) . k * pow2 64 = t3} ->
  prime_: pos {prime_ > 3 /\
    (prime_ = 115792089210356248762697446949407573529996955224135760342422259061068512044369 \/ prime_ = prime256)} ->
  Lemma (t3 * modp_inv2_prime (pow2 64) prime_  % prime_ = (t3 / pow2 64) % prime_)


let lemma_division_is_multiplication t3 prime_ =
  let remainder = t3 / pow2 64 in
  let prime2 = 115792089210356248762697446949407573529996955224135760342422259061068512044369 in
    assert_norm((modp_inv2_prime (pow2 64) prime256 * pow2 64) % prime256 = 1);
    assert_norm ((modp_inv2_prime (pow2 64) prime2 * pow2 64) % prime2 = 1);
  let k =  modp_inv2_prime (pow2 64) prime_ * pow2 64 in
  modulo_distributivity_mult remainder k prime_;
  lemma_mod_twice remainder prime_;
  assert_by_tactic (t3 / pow2 64 * (modp_inv2_prime (pow2 64) prime_ * pow2 64) == t3/ pow2 64 * pow2 64 * modp_inv2_prime (pow2 64) prime_) canon



val lemma_reduce_mod_by_sub3 : t: nat -> Lemma ((t + (t % pow2 64) * prime256) % pow2 64 == 0)

let lemma_reduce_mod_by_sub3 t =
  let t_ = (t + (t % pow2 64) * prime256) % pow2 64 in
  lemma_mod_add_distr t ((t % pow2 64) * prime256) (pow2 64);
  lemma_mod_mul_distr_l t prime256 (pow2 64);
    assert(t_ == (t + (t * prime256) % pow2 64) % pow2 64);
  lemma_mod_add_distr t (t * prime256) (pow2 64);
    assert_norm(t * (prime256 + 1) % pow2 64 == 0)


val mult_one_round: t: nat -> co: nat{t % prime256 == co% prime256}  -> Lemma (
  let result = (t + (t % pow2 64) * prime256) / pow2 64 % prime256 in
  result == (co * modp_inv2 (pow2 64)) % prime256)

let mult_one_round t co =
let t1 = t % pow2 64 in
    let t2 = t1 * prime256 in
    let t3 = t + t2 in
      modulo_addition_lemma t prime256 (t % pow2 64);
      assert(t3 % prime256 = co % prime256);
      lemma_div_mod t3 (pow2 64);
      lemma_reduce_mod_by_sub3 t;
      assert(t3 % pow2 64 == 0);
      assert(let rem = t3/ pow2 64 in rem * pow2 64 = t3);
      assert(exists (k: nat). k * pow2 64 = t3);
      assert_norm (prime256 > 3);
      lemma_division_is_multiplication t3 prime256;
      lemma_multiplication_to_same_number t3 co (modp_inv2 (pow2 64)) prime256


val lemma_reduce_mod_ecdsa_prime:
  prime : nat {prime = 115792089210356248762697446949407573529996955224135760342422259061068512044369} ->
  t: nat -> k0: nat {k0 = min_one_prime (pow2 64) (- prime)} ->  Lemma (
  (t + prime * (k0 * (t % pow2 64) % pow2 64)) % pow2 64 == 0)

let lemma_reduce_mod_ecdsa_prime prime t k0 =
  let f = prime * (k0 * (t % pow2 64) % pow2 64) in
  let t0 = (t + f) % pow2 64 in
  lemma_mod_add_distr t f (pow2 64);
  modulo_addition_lemma t (pow2 64) f;
  lemma_mod_mul_distr_r k0 t (pow2 64);
  lemma_mod_mul_distr_r prime (k0 * t) (pow2 64);
    assert_by_tactic(prime * (k0 * t) == (prime * k0) * t) canon;
  lemma_mod_mul_distr_l (prime * k0) t (pow2 64);
    assert_norm (exp #(pow2 64) 884452912994769583 (pow2 64  - 1)  = 14758798090332847183);
  lemma_mod_mul_distr_l (-1) t (pow2 64);
  lemma_mod_add_distr t (-t) (pow2 64)


val mult_one_round_ecdsa_prime: t: nat ->
  prime: pos {prime = 115792089210356248762697446949407573529996955224135760342422259061068512044369} ->
  co: nat {t % prime == co % prime} -> k0: nat {k0 = min_one_prime (pow2 64) (- prime)} -> Lemma (
    let result = (t + prime * ((k0 * (t % pow2 64)) % pow2 64)) / pow2 64 in
    result % prime == (co * modp_inv2_prime (pow2 64) prime) % prime)

let mult_one_round_ecdsa_prime t prime co k0 =
  let t2 = ((k0 * (t % pow2 64)) % pow2 64) * prime in
  let t3 = t + t2 in
    modulo_addition_lemma t prime ((k0 * (t % pow2 64)) % pow2 64);
    lemma_div_mod t3 (pow2 64);
    lemma_reduce_mod_ecdsa_prime prime t k0;
      assert(let rem = t3/ pow2 64 in rem * pow2 64 = t3);
      assert(exists (k: nat). k * pow2 64 = t3);
    lemma_division_is_multiplication t3 prime;
    lemma_multiplication_to_same_number t3 co (modp_inv2_prime (pow2 64) prime) prime


val lemma_brackets : a: int -> b: int -> c: int -> Lemma (a * b * c = a * (b * c))
let lemma_brackets a b c = ()

val lemma_twice_brackets: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> h: int-> Lemma (
  (a * b * c) * (d * e * f) * h = a * b * c * d * e * f * h)
let lemma_twice_brackets a b c d e f h = ()


#reset-options " --z3rlimit 300"

val modulo_distributivity_mult2: a: int -> b: int -> c: int -> d: pos -> Lemma (((a % d) * (b % d) * c) % d = (a * b * c) % d)
let modulo_distributivity_mult2 a b c d =
  calc (==)
  {
    ((a % d) * (b % d) * c) % d;
    (==)
    {assert_by_tactic (((a % d) * (b % d) * c) == ((a % d) * ((b % d) * c))) canon}
    ((a % d) * ((b % d) * c)) % d;
    (==)
    {lemma_mod_mul_distr_l a ((b % d) * c) d}
    (a * ((b % d) * c)) % d;
    (==)
    {assert_by_tactic (a * ((b % d) * c) == (a * (b % d) * c)) canon}
    (a * (b % d) * c) % d;
    (==)
    {assert_by_tactic (a * (b % d) * c == (b % d) * (a * c)) canon}

    ((b % d) * (a * c)) % d;
    (==)
    {lemma_mod_mul_distr_l b (a * c) d; assert_by_tactic (b * (a * c) == a * b * c) canon }
    (a * b * c) % d;
  }


let mul_lemma_1 (a: nat) (c: nat) (b: pos) : Lemma (requires (a < c)) (ensures (a * b < c * b)) = ()

let mul_lemma_ (a: nat) (b: nat) (c: nat) : Lemma (requires (a < c /\ b < c)) (ensures (a * b < c * c)) = ()

let mul_lemma_2 (a: nat) (c: nat) (b: pos) : Lemma (requires (a <= c)) (ensures (a * b <= c * b)) = ()

let mul_lemma_4 (a: nat) (b: nat) (c: nat) (d: nat) : Lemma (requires (a <= c && b <= d)) (ensures (a * b <= c * d)) = ()


(*This code is taken from Curve25519, written by Polubelova M *)
val lemma_cswap2_step:
    bit:uint64{v bit <= 1}
  -> p1:uint64
  -> p2:uint64
  -> Lemma (
      let mask = u64 0 -. bit in
      let dummy = mask &. (p1 ^. p2) in
      let p1' = p1 ^. dummy in
      let p2' = p2 ^. dummy in
      if v bit = 1 then p1' == p2 /\ p2' == p1 else p1' == p1 /\ p2' == p2)

let lemma_cswap2_step bit p1 p2 =
  let mask = u64 0 -. bit in
  assert (v bit == 0 ==> v mask == 0);
  assert (v bit == 1 ==> v mask == pow2 64 - 1);
  let dummy = mask &. (p1 ^. p2) in
  logand_lemma mask (p1 ^. p2);
  assert (v bit == 1 ==> v dummy == v (p1 ^. p2));
  assert (v bit == 0 ==> v dummy == 0);
  let p1' = p1 ^. dummy in
  (* uintv_extensionality dummy (if v bit = 1 then (p1 ^. p2) else u64 0); *)
  logxor_lemma p1 p2;
  let p2' = p2 ^. dummy in
  logxor_lemma p2 p1

(* </> *)
