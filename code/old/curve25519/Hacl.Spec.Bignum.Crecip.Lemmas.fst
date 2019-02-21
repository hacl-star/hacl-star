module Hacl.Spec.Bignum.Crecip.Lemmas

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open Spec.Curve25519

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val lemma_op_Star_Star_def_0: x:elem -> Lemma (Spec.Curve25519.(x ** 1 = x))
#set-options "--initial_fuel 1 --max_fuel 1"
let lemma_op_Star_Star_def_0 x = ()

#set-options "--initial_fuel 0 --max_fuel 0"

val lemma_op_Star_Star_def_1: x:elem -> n:int{n > 1 /\ n % 2 = 0} -> Lemma (Spec.Curve25519.(x ** n = op_Star_Star (x *@ x) (n / 2) ))
#set-options "--initial_fuel 1 --max_fuel 1"
let lemma_op_Star_Star_def_1 x n = ()

#set-options "--initial_fuel 0 --max_fuel 0"
val lemma_op_Star_Star_def_1': x:elem -> n:int{n > 1 /\ n % 2 = 1} -> 
  Lemma (Spec.Curve25519.((n-1)/2 >= 1 /\ x ** n = x *@ (op_Star_Star (x *@ x) ((n-1) / 2)) ))
#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"
let lemma_op_Star_Star_def_1' x n = ()

#set-options "--initial_fuel 0 --max_fuel 0"

val exp: x:elem -> n:nat -> Tot elem (decreases n)
let rec exp x n =
  if n = 0 then one
  else x *@ (exp x (n-1))

#reset-options "--max_fuel 0"
val lemma_exp_def_0: x:elem -> Lemma (Spec.Curve25519.(exp x 0 = one))
val lemma_exp_def_1: x:elem -> n:pos -> Lemma (Spec.Curve25519.(exp x n = x *@ exp x (n-1)))
#reset-options "--max_fuel 1 --initial_fuel 1 --z3rlimit 20"
let lemma_exp_def_0 x = ()
let lemma_exp_def_1 x n = ()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

let lemma_op_Star_At_assoc a b c : Lemma ( (a *@ b) *@ c = a *@ (b *@ c)) =
  let open FStar.Mul in
  let ab = a * b in
  cut ( (a *@ b) *@ c = (((ab) % prime) * c) % prime);
  Math.Lemmas.lemma_mod_mul_distr_l ab c prime;
  Math.Lemmas.lemma_mod_mul_distr_l (op_Multiply b c) a prime;
  Math.Lemmas.paren_mul_right a b c

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_exp_add: x:elem -> n:nat -> m:nat -> Lemma
  (requires True)
  (ensures (exp x n *@ exp x m) = exp x (n+m))
  (decreases n)
let rec lemma_exp_add x n m =
  if n = 0 then (lemma_exp_def_0 x; Math.Lemmas.modulo_lemma (exp x m) prime)
  else (
    lemma_exp_add x (n-1) m;
    lemma_exp_def_1 x n;
    lemma_exp_def_1 x (n+m);
    lemma_op_Star_At_assoc x (exp x (n-1)) (exp x m)
  )

val lemma_exp_double: x:elem -> n:nat -> Lemma
  (requires True)
  (ensures (exp (x *@ x) n = exp x (n+n)))
  (decreases n)
let rec lemma_exp_double x n =
  if n = 0 then (
    cut (n+n = 0);
    lemma_exp_def_0 (x *@ x);
    lemma_exp_def_0 (x)
  ) else (
    lemma_exp_double x (n-1);
    lemma_exp_def_1 (x *@ x) n;
    lemma_exp_def_1 x (n+n);
    lemma_exp_def_1 x (n+n-1);
    cut (exp x (n+n) = x *@ (x *@ exp x (n+n-2)));
    lemma_op_Star_At_assoc x x (exp x (n+n-2)))

val lemma_exp_mul: x:elem -> n:nat -> m:nat -> Lemma
  (requires (True))
  (ensures (exp (exp x n) m = exp x (op_Multiply n m)))
  (decreases m)
let rec lemma_exp_mul x n m =
  if m = 0 then (
    lemma_exp_def_0 (exp x n);
    lemma_exp_def_0 (x)
  ) else (
    cut (m > 0);
    let open FStar.Mul in
    lemma_exp_mul x n (m-1);
    lemma_exp_def_1 (exp x n) m;
    lemma_exp_add x n (n * (m-1)))


val lemma_exp_eq: x:elem -> n:pos -> Lemma
  (requires (True))
  (ensures (exp x n = Spec.Curve25519.op_Star_Star x n))
  (decreases n)
let rec lemma_exp_eq x n =
  if n = 1 then (
    lemma_exp_def_1 x 1; lemma_exp_def_0 x; Math.Lemmas.modulo_lemma x prime;
    lemma_op_Star_Star_def_0 x)
  else if n % 2 = 0 then (
    cut (n > 1);
    lemma_op_Star_Star_def_1 x n;
    cut (Spec.Curve25519.(x ** n = (x *@ x) ** (n / 2)));
    lemma_exp_eq (x *@ x) (n / 2);
    lemma_exp_double x (n/2)
  ) else (
    cut (n > 1 /\ n%2 = 1);
    lemma_op_Star_Star_def_1' x n;
    cut (Spec.Curve25519.(x ** n = x *@ ((x *@ x) ** (n / 2))));
    lemma_exp_eq (x *@ x) (n / 2);
    lemma_exp_double x (n/2);
    Math.Lemmas.lemma_div_mod n 2;
    lemma_exp_def_1 x n
  )
