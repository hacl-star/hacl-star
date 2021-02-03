module Lib.NatMod

open FStar.Mul

module LE = Lib.Exponentiation

#set-options "--z3rlimit 10 --fuel 0 --ifuel 0"

let mk_nat_group : LE.exp int = {
  LE.one = 1;
  LE.fmul = FStar.Mul.op_Star;
  LE.lemma_one = Math.Lemmas.mul_one_right_is_same;
  LE.lemma_fmul_assoc = Math.Lemmas.paren_mul_right;
  LE.lemma_fmul_comm = Math.Lemmas.swap_mul;
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
  Lemma (pow a b == LE.pow mk_nat_group a b)

val lemma_pow_add: x:int -> n:nat -> m:nat -> Lemma (pow x n * pow x m = pow x (n + m))

val lemma_pow_mul: x:int -> n:nat -> m:nat -> Lemma (pow (pow x n) m = pow x (n * m))

val lemma_pow_double: a:int -> b:nat -> Lemma (pow (a * a) b == pow a (b + b))

val lemma_pow_mul_base: a:int -> b:int -> n:nat -> Lemma (pow a n * pow b n == pow (a * b) n)

val lemma_pow_mod_base: a:int -> b:nat -> n:pos -> Lemma (pow a b % n == pow (a % n) b % n)



let nat_mod (m:pos) = n:nat{n < m}

let one_mod (#m:pos) : nat_mod m = 1 % m
let mul_mod (#m:pos) (a:nat_mod m) (b:nat_mod m) : nat_mod m = a * b % m

val lemma_one_mod: #m:pos -> a:nat_mod m -> Lemma (mul_mod a one_mod == a)

val lemma_mul_mod_assoc: #m:pos -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m ->
  Lemma (mul_mod (mul_mod a b) c == mul_mod a (mul_mod b c))

val lemma_mul_mod_comm: #m:pos -> a:nat_mod m -> b:nat_mod m ->
  Lemma (mul_mod a b == mul_mod b a)

let mk_nat_mod_group (m:pos) : LE.exp (nat_mod m) = {
  LE.one = one_mod;
  LE.fmul = mul_mod;
  LE.lemma_one = lemma_one_mod;
  LE.lemma_fmul_assoc = lemma_mul_mod_assoc;
  LE.lemma_fmul_comm = lemma_mul_mod_comm;
  }

val pow_mod: #m:pos -> a:nat_mod m -> b:pos -> nat_mod m

val lemma_pow_mod: #m:pos -> a:nat_mod m -> b:pos -> Lemma (pow a b % m == pow_mod #m a b)

val lemma_pow_nat_mod_is_pow: #n:pos -> a:nat_mod n -> b:pos ->
  Lemma (pow a b % n == LE.pow (mk_nat_mod_group n) a b)
