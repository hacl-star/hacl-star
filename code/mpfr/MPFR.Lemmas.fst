module MPFR.Lemmas

open FStar.Mul

#set-options "--z3refresh --z3rlimit 5 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* Nonlinear arithmetic *)
val lemma_paren_mul_left: a:int -> b:int -> c:int -> Lemma
    (a * b * c = (a * b) * c)

val lemma_paren_mul_right: a:int -> b:int -> c:int -> Lemma
    (a * b * c = a * (b * c))

val lemma_mul_le_left: a:nat -> b:int -> c:int -> Lemma
    (requires (b <= c))
    (ensures  (a * b <= a * c))

val lemma_mul_le_right: a:nat -> b:int -> c:int -> Lemma
    (requires (b <= c))
    (ensures  (b * a <= c * a))

val lemma_mul_lt_left: a:pos -> b:int -> c:int -> Lemma
    (requires (b < c))
    (ensures  (a * b < a * c))

val lemma_mul_lt_right: a:pos -> b:int -> c:int -> Lemma
    (requires (b < c))
    (ensures  (b * a < c * a))

val lemma_distr_add_left: a:int -> b:int -> c:int -> Lemma
    ((a + b) * c = a * c + b * c)

val lemma_distr_add_right: a:int -> b:int -> c:int -> Lemma
    (a * (b + c) = a * b + a * c)

val lemma_distr_sub_left: a:int -> b:int -> c:int -> Lemma
    ((a - b) * c = a * c - b * c)

val lemma_distr_sub_right: a:int -> b:int -> c:int -> Lemma
    (a * (b - c) = a * b - a * c)

(* Division and modulo *)
val lemma_small_div: a:nat -> b:pos -> Lemma
    (requires (a < b))
    (ensures  (a / b = 0))

val lemma_small_mod: a:nat -> b:pos -> Lemma
    (requires (a < b))
    (ensures  (a % b = a))

val lemma_mul_div: a:nat -> b:pos -> Lemma
    ((a * b) / b = a)

val lemma_mul_mod: a:nat -> b:pos -> Lemma
    ((a * b) % b = 0)

val lemma_div_lt: a:nat -> b:nat -> d:pos -> Lemma
    (requires (a < b /\ b % d = 0))
    (ensures  (a / d < b / d))

val lemma_div_le: a:nat -> b:nat -> d:pos -> Lemma
    (requires (a <= b))
    (ensures  (a / d <= b / d))

val lemma_div_div: a:nat -> b:pos -> c:pos -> Lemma
    ((a / b) / c = a / (b * c))

val lemma_mod_distr: a:nat -> b:nat -> c:pos -> Lemma
    ((a + b) % c = (a % c + b % c) % c)
    
val lemma_mod_div: a:nat -> b:pos -> c:pos -> Lemma 
    ((a % (b * c)) / b = (a / b) % c)

val lemma_mod_mod: a:nat -> b:pos -> c:pos -> Lemma
    ((a % (b * c)) % b = a % b)

(* pow2 proprieties *)
val lemma_pow2_le: n:nat -> m:nat -> Lemma
    (requires (n <= m))
    (ensures  (pow2 n <= pow2 m))

val lemma_pow2_lt: n:nat -> m:nat -> Lemma
    (requires (n < m))
    (ensures  (pow2 n < pow2 m))
    
val lemma_pow2_mul: n:nat -> m:nat -> Lemma
    (pow2 n * pow2 m = pow2 (n + m))

val lemma_pow2_small_div: n:nat -> m:nat -> Lemma
    (requires (n < m))
    (ensures  (pow2 n / pow2 m = 0))

val lemma_pow2_small_mod: n:nat -> m:nat -> Lemma
    (requires (n < m))
    (ensures  (pow2 n % pow2 m = pow2 n))

val lemma_pow2_div: n:nat -> m:nat -> Lemma
    (requires (m <= n))
    (ensures  (pow2 n / pow2 m = pow2 (n - m)))

val lemma_pow2_mod: n:nat -> m:nat -> Lemma
    (requires (m <= n))
    (ensures  (pow2 n % pow2 m = 0))

val lemma_pow2_double: n:nat -> Lemma
    (pow2 n + pow2 n = pow2 (n + 1))

val lemma_pow2_div_lt: a:nat -> b:nat -> d:nat -> Lemma
    (requires (a < pow2 b /\ d <= b))
    (ensures  (a / pow2 d < pow2 (b - d)))
    
val lemma_pow2_mod_div: a:nat -> b:nat -> c:nat -> Lemma
    (requires (b >= c))
    (ensures  ((a % pow2 b) / pow2 c = (a / pow2 c) % (pow2 (b - c))))

val lemma_pow2_mod_mod: a:nat -> b:nat -> c:nat -> Lemma
    (requires (b >= c))
    (ensures  ((a % pow2 b) % pow2 c = a % pow2 c))
    

(* Proofs *)
(* Nonlinear arithmetic *)
let lemma_paren_mul_left a b c = ()
let lemma_paren_mul_right a b c = ()
let lemma_mul_le_left a b c = ()
let lemma_mul_le_right a b c = ()
let lemma_mul_lt_left a b c = ()
let lemma_mul_lt_right a b c = ()
let lemma_distr_add_left a b c = ()
let lemma_distr_add_right a b c = ()
let lemma_distr_sub_left a b c = ()
let lemma_distr_sub_right a b c = ()

(* Division and modulo *)
val lemma_euclidean: a:nat -> b:pos -> Lemma
    (a = (a / b) * b + a % b)
let lemma_euclidean a b = ()
val lemma_add_div: a:nat -> n:int -> d:pos -> Lemma
    (requires (a + n * d >= 0))
    (ensures  ((a + n * d) / d = a / d + n))
let lemma_add_div a n d = assert(a / d + n - 1 < (a + n * d) / d /\ (a + n * d) / d < a / d + n + 1)
val lemma_add_mod: a:nat -> n:int -> d:pos -> Lemma
    (requires (a + n * d >= 0))
    (ensures  ((a + n * d) % d = a % d))
let lemma_add_mod a n d = lemma_add_div a n d

let lemma_small_div a b = ()
let lemma_small_mod a b = ()
let lemma_mul_div a b = lemma_add_div 0 a b
let lemma_mul_mod a b = lemma_mul_div a b
let lemma_div_lt a b d = assert(a / d >= b / d ==> a >= b)
let lemma_div_le a b d = lemma_add_div (b - a / d * d) (a / d) d

let lemma_div_div a b c =
    lemma_euclidean (a / b) c;
    lemma_add_div (((a / b) % c) * b + a % b) ((a / b) / c) (b * c);
    lemma_distr_sub_left c 1 b;
    lemma_small_div (((a / b) % c) * b + a % b) (b * c)

let lemma_mod_distr a b c =
    lemma_euclidean a c;
    lemma_add_mod (a % c + b % c) (a / c + b / c) c

let lemma_mod_div a b c =
    lemma_euclidean a (b * c);
    lemma_add_div a (- (a / (b * c)) * c) b;
    assert((a % (b * c)) / b = a / b - (a / (b * c)) * c);
    lemma_div_div a b c;
    lemma_euclidean (a / b) c

let lemma_mod_mod a b c =
    lemma_euclidean a (b * c);
    lemma_add_mod a (- (a / (b * c)) * c) b

(* pow2 proprieties *)
let lemma_pow2_le n m = FStar.Math.Lemmas.pow2_le_compat m n
let lemma_pow2_lt n m = FStar.Math.Lemmas.pow2_lt_compat m n
let lemma_pow2_mul n m = FStar.Math.Lemmas.pow2_plus n m
let lemma_pow2_small_div n m =
    lemma_pow2_lt n m;
    lemma_small_div (pow2 n) (pow2 m)
let lemma_pow2_small_mod n m =
    lemma_pow2_lt n m;
    lemma_small_mod  (pow2 n) (pow2 m)
let lemma_pow2_div n m = FStar.Math.Lemmas.pow2_minus n m
let lemma_pow2_mod n m = 
    lemma_pow2_mul (n - m) m;
    lemma_mul_mod (pow2 (n - m)) (pow2 m)
let lemma_pow2_double n = ()
let lemma_pow2_div_lt a b d = 
    lemma_pow2_div b d;
    lemma_pow2_mod b d;
    lemma_div_lt a (pow2 b) (pow2 d)
let lemma_pow2_mod_div a b c =
    lemma_pow2_mul c (b - c);
    lemma_mod_div a (pow2 c) (pow2 (b - c))
let lemma_pow2_mod_mod a b c =
    lemma_pow2_mul c (b - c);
    lemma_mod_mod a (pow2 c) (pow2 (b - c))
