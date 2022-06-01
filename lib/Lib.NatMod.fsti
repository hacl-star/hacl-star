module Lib.NatMod

open FStar.Mul

module Fermat = FStar.Math.Fermat
module Euclid = FStar.Math.Euclid

module LE = Lib.Exponentiation

#set-options "--z3rlimit 10 --fuel 0 --ifuel 0"

let mk_nat_comm_monoid : LE.comm_monoid int = {
  LE.one = 1;
  LE.mul = FStar.Mul.op_Star;
  LE.lemma_one = Math.Lemmas.mul_one_right_is_same;
  LE.lemma_mul_assoc = Math.Lemmas.paren_mul_right;
  LE.lemma_mul_comm = Math.Lemmas.swap_mul;
  }


let rec pow (x:int) (n:nat) : Tot int =
  if n = 0 then 1
  else x * pow x (n - 1)

val lemma_pow0: a:int -> Lemma (pow a 0 = 1)
val lemma_pow1: a:int -> Lemma (pow a 1 = a)
val lemma_pow_unfold: a:int -> b:pos -> Lemma (a * pow a (b - 1) == pow a b)

val lemma_pow_gt_zero: a:pos -> b:nat -> Lemma (pow a b > 0) [SMTPat (pow a b)]
val lemma_pow_ge_zero: a:nat -> b:nat -> Lemma (pow a b >= 0) [SMTPat (pow a b)]

val lemma_pow_nat_is_pow: a:int -> b:nat ->
  Lemma (pow a b == LE.pow mk_nat_comm_monoid a b)

val lemma_pow_one: b:nat -> Lemma (pow 1 b = 1)

val lemma_pow_add: x:int -> n:nat -> m:nat -> Lemma (pow x n * pow x m = pow x (n + m))

val lemma_pow_mul: x:int -> n:nat -> m:nat -> Lemma (pow (pow x n) m = pow x (n * m))

val lemma_pow_double: a:int -> b:nat -> Lemma (pow (a * a) b == pow a (b + b))

val lemma_pow_mul_base: a:int -> b:int -> n:nat -> Lemma (pow a n * pow b n == pow (a * b) n)

val lemma_pow_mod_base: a:int -> b:nat -> n:pos -> Lemma (pow a b % n == pow (a % n) b % n)



let nat_mod (m:pos) = n:nat{n < m}

let one_mod (#m:pos) : nat_mod m = 1 % m
let mul_mod (#m:pos) (a:nat_mod m) (b:nat_mod m) : nat_mod m = a * b % m
let add_mod (#m:pos) (a:nat_mod m) (b:nat_mod m) : nat_mod m = (a + b) % m
let sub_mod (#m:pos) (a:nat_mod m) (b:nat_mod m) : nat_mod m = (a - b) % m

val lemma_mul_mod_one: #m:pos -> a:nat_mod m -> Lemma (mul_mod a one_mod == a)

val lemma_mul_mod_assoc: #m:pos -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m ->
  Lemma (mul_mod (mul_mod a b) c == mul_mod a (mul_mod b c))

val lemma_mul_mod_comm: #m:pos -> a:nat_mod m -> b:nat_mod m ->
  Lemma (mul_mod a b == mul_mod b a)

let mk_nat_mod_comm_monoid (m:pos) : LE.comm_monoid (nat_mod m) = {
  LE.one = one_mod;
  LE.mul = mul_mod;
  LE.lemma_one = lemma_mul_mod_one;
  LE.lemma_mul_assoc = lemma_mul_mod_assoc;
  LE.lemma_mul_comm = lemma_mul_mod_comm;
  }

val pow_mod: #m:pos{1 < m} -> a:nat_mod m -> b:nat -> nat_mod m

val lemma_pow_mod: #m:pos{1 < m} -> a:nat_mod m -> b:nat -> Lemma (pow a b % m == pow_mod #m a b)

val lemma_pow_nat_mod_is_pow: #n:pos{1 < n} -> a:nat_mod n -> b:nat ->
  Lemma (pow a b % n == LE.pow (mk_nat_mod_comm_monoid n) a b)


val lemma_add_mod_one: #m:pos -> a:nat_mod m -> Lemma (add_mod a 0 == a)

val lemma_add_mod_assoc: #m:pos -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m ->
  Lemma (add_mod (add_mod a b) c == add_mod a (add_mod b c))

val lemma_add_mod_comm: #m:pos -> a:nat_mod m -> b:nat_mod m ->
  Lemma (add_mod a b == add_mod b a)


val lemma_mod_distributivity_add_right: #m:pos -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m ->
  Lemma (mul_mod a (add_mod b c) == add_mod (mul_mod a b) (mul_mod a c))

val lemma_mod_distributivity_add_left: #m:pos -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m ->
  Lemma (mul_mod (add_mod a b) c == add_mod (mul_mod a c) (mul_mod b c))

val lemma_mod_distributivity_sub_right: #m:pos -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m ->
  Lemma (mul_mod a (sub_mod b c) == sub_mod (mul_mod a b) (mul_mod a c))

val lemma_mod_distributivity_sub_left: #m:pos -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m ->
  Lemma (mul_mod (sub_mod a b) c == sub_mod (mul_mod a c) (mul_mod b c))


let prime = m:pos{1 < m /\ Euclid.is_prime m}
let inv_mod (#m:prime) (a:nat_mod m) : nat_mod m = pow_mod #m a (m - 2)
let div_mod (#m:prime) (a:nat_mod m) (b:nat_mod m) : nat_mod m = mul_mod a (inv_mod b)

val lemma_inv_mod_both: #m:prime -> a:nat_mod m -> b:nat_mod m ->
  Lemma (inv_mod (mul_mod a b) == mul_mod (inv_mod a) (inv_mod b))

val lemma_div_mod_prime: #m:prime -> a:nat_mod m{a <> 0} -> Lemma (div_mod a a == 1)
val lemma_div_mod_prime_one: #m:prime -> a:nat_mod m -> Lemma (div_mod a 1 == a)

val lemma_div_mod_prime_cancel: #m:prime -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m{c <> 0} ->
  Lemma (div_mod (mul_mod a c) (mul_mod c b) == div_mod a b)

val lemma_div_mod_prime_to_one_denominator: #m:prime -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m{c <> 0} -> d:nat_mod m{d <> 0} ->
  Lemma (mul_mod (div_mod a c) (div_mod b d) == div_mod (mul_mod a b) (mul_mod c d))

val lemma_div_mod_eq_mul_mod: #m:prime -> a:nat_mod m -> b:nat_mod m{b <> 0} -> c:nat_mod m ->
  Lemma ((div_mod a b = c) == (a = mul_mod c b))
