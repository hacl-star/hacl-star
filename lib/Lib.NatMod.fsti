module Lib.NatMod

open FStar.Mul

#set-options "--z3rlimit 10 --fuel 0 --ifuel 0"

let nat_mod (m:pos) = n:nat{n < m}

let mul_mod (#m:pos) (a:nat_mod m) (b:nat_mod m) : nat_mod m =
  a * b % m

val pow_mod: #m:pos -> a:nat_mod m -> b:pos -> nat_mod m

let rec pow (x:int) (n:nat) : Tot int =
  if n = 0 then 1
  else x * pow x (n - 1)

val lemma_pow0: a:int -> Lemma (pow a 0 = 1)
val lemma_pow1: a:int -> Lemma (pow a 1 = a)
val lemma_pow_unfold: a:int -> b:pos -> Lemma (a * pow a (b - 1) == pow a b)

val lemma_pow_greater: a:pos -> b:nat -> Lemma (pow a b > 0) [SMTPat (pow a b)]

val lemma_pow_add: x:int -> n:nat -> m:nat -> Lemma (pow x n * pow x m = pow x (n + m))

val lemma_pow_double: a:int -> b:nat -> Lemma (pow (a * a) b == pow a (b + b))

val lemma_pow_mul_base: a:int -> b:int -> n:nat -> Lemma (pow a n * pow b n == pow (a * b) n)

val lemma_pow_mod_base: a:int -> b:nat -> n:pos -> Lemma (pow a b % n == pow (a % n) b % n)

val lemma_pow_mod: #m:pos -> a:nat_mod m -> b:pos -> Lemma (pow a b % m == pow_mod #m a b)
