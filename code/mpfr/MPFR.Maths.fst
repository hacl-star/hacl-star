module MPFR.Maths

open FStar.Mul

#set-options "--z3refresh --z3rlimit 5 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* Nonlinear arithmetic *)
val lemma_paren_mul_left: a:int -> b:int -> c:int -> Lemma
    (a * b * c = (a * b) * c)
let lemma_paren_mul_left a b c = ()

val lemma_paren_mul_right: a:int -> b:int -> c:int -> Lemma
    (a * b * c = a * (b * c))
let lemma_paren_mul_right a b c = ()

val lemma_mul_le_left: a:nat -> b:int -> c:int -> Lemma
    (requires (b <= c))
    (ensures  (a * b <= a * c))
let lemma_mul_le_left a b c = ()

val lemma_mul_le_right: a:nat -> b:int -> c:int -> Lemma
    (requires (b <= c))
    (ensures  (b * a <= c * a))
let lemma_mul_le_right a b c = ()

val lemma_mul_lt_left: a:pos -> b:int -> c:int -> Lemma
    (requires (b < c))
    (ensures  (a * b < a * c))
let lemma_mul_lt_left a b c = ()

val lemma_mul_lt_right: a:pos -> b:int -> c:int -> Lemma
    (requires (b < c))
    (ensures  (b * a < c * a))
let lemma_mul_lt_right a b c = ()

val lemma_distr_add_left: a:int -> b:int -> c:int -> Lemma
    ((a + b) * c = a * c + b * c)
let lemma_distr_add_left a b c = ()

val lemma_distr_add_right: a:int -> b:int -> c:int -> Lemma
    (a * (b + c) = a * b + a * c)
let lemma_distr_add_right a b c = ()

val lemma_distr_sub_left: a:int -> b:int -> c:int -> Lemma
    ((a - b) * c = a * c - b * c)
let lemma_distr_sub_left a b c = ()

val lemma_distr_sub_right: a:int -> b:int -> c:int -> Lemma
    (a * (b - c) = a * b - a * c)
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

val lemma_small_div: a:nat -> b:pos -> Lemma
    (requires (a < b))
    (ensures  (a / b = 0))
let lemma_small_div a b = ()

val lemma_small_mod: a:nat -> b:pos -> Lemma
    (requires (a < b))
    (ensures  (a % b = a))
let lemma_small_mod a b = ()

val lemma_multiple_div: a:nat -> b:pos -> Lemma
    ((a * b) / b = a)
let lemma_multiple_div a b = lemma_add_div 0 a b

val lemma_multiple_mod: a:nat -> b:pos -> Lemma
    ((a * b) % b = 0)
let lemma_multiple_mod a b = lemma_multiple_div a b

val lemma_mul_mod_zero: a:nat -> b:nat -> c:pos -> Lemma
    (requires (a % c = 0 \/ b % c = 0))
    (ensures  ((a * b) % c = 0))
    (decreases (b % c))

let rec lemma_mul_mod_zero a b c =
    if b % c > 0 then lemma_mul_mod_zero b a c else lemma_multiple_mod (a * (b / c)) c

val lemma_div_lt: a:nat -> b:nat -> d:pos -> Lemma
    (requires (a < b /\ b % d = 0))
    (ensures  (a / d < b / d))
let lemma_div_lt a b d = assert(a / d >= b / d ==> a >= b)

val lemma_div_le: a:nat -> b:nat -> d:pos -> Lemma
    (requires (a <= b))
    (ensures  (a / d <= b / d))
let lemma_div_le a b d = lemma_add_div (b - a / d * d) (a / d) d

val lemma_div_distr: a:nat -> b:nat -> c:pos -> Lemma
    (requires (a % c = 0))
    (ensures  ((a + b) / c = a / c + b / c))
let lemma_div_distr a b c = lemma_add_div b (a / c) c

val lemma_mod_distr: a:nat -> b:nat -> c:pos -> Lemma
    ((a + b) % c = (a % c + b % c) % c)
    
let lemma_mod_distr a b c =
    lemma_euclidean a c;
    //! assert((a + b) / c = ((a / c + b / c) * c + (a % c + b % c)) / c);
    lemma_add_mod (a % c + b % c) (a / c + b / c) c

val lemma_mod_distr_zero: a:nat -> b:nat -> c:pos -> Lemma
    (requires (a % c = 0 /\ b % c = 0))
    (ensures  ((a + b) % c = 0))

let lemma_mod_distr_zero a b c = lemma_mod_distr a b c

val lemma_div_div: a:nat -> b:pos -> c:pos -> Lemma
    ((a / b) / c = a / (b * c))
    
let lemma_div_div a b c =
    lemma_euclidean a b;
    //! assert(a = (a / b) * b + a % b);
    lemma_euclidean (a / b) c;
    //! assert(a / b = ((a / b) / c) * c + (a / b) % c);
    //! assert(a = ((a / b) / c) * c * b + ((a / b) % c) * b + a % b);
    lemma_add_div (((a / b) % c) * b + a % b) ((a / b) / c) (b * c);
    //! assert(a / (b * c) = (a / b) / c + (((a / b) % c) * b + a % b) / (b * c));
    lemma_distr_sub_left c 1 b;
    //! assert(((a / b) % c) * b + a % b <= (c - 1) * b + (b - 1));
    lemma_small_div (((a / b) % c) * b + a % b) (b * c)

val lemma_mul_div: a:nat -> b:nat -> c:pos -> Lemma
    (requires (a % c = 0))
    (ensures  ((a * b) / c = (a / c) * b))
    
let lemma_mul_div a b c =
    lemma_euclidean a c;
    //! assert((a * b) / c = ((a / c) * c * b) / c);
    lemma_multiple_div ((a / c) * b) c

val lemma_mul_mod: a:nat -> b:nat -> c:pos -> Lemma
    (requires (a % c = 0))
    (ensures  ((a * b) % c = 0))
let lemma_mul_mod a b c = lemma_mul_div a b c
    
val lemma_mod_div: a:nat -> b:pos -> c:pos -> Lemma 
    ((a % (b * c)) / b = (a / b) % c)
    
let lemma_mod_div a b c =
    lemma_euclidean a (b * c);
    //! assert(a = (a / (b * c)) * (b * c) + a % (b * c));
    lemma_add_div a (- (a / (b * c)) * c) b;
    assert((a % (b * c)) / b = a / b - (a / (b * c)) * c);
    lemma_div_div a b c;
    //! assert((a % (b * c)) / b = a / b - ((a / b) / c) * c);
    lemma_euclidean (a / b) c

val lemma_mod_mod: a:nat -> b:pos -> c:pos -> Lemma
    ((a % (b * c)) % b = a % b)
let lemma_mod_mod a b c =
    lemma_euclidean a (b * c);
    lemma_add_mod a (- (a / (b * c)) * c) b

(* pow2 proprieties *)
val lemma_pow2_le: n:nat -> m:nat -> Lemma
    (requires (n <= m))
    (ensures  (pow2 n <= pow2 m))
let lemma_pow2_le n m = FStar.Math.Lemmas.pow2_le_compat m n

val lemma_pow2_lt: n:nat -> m:nat -> Lemma
    (requires (n < m))
    (ensures  (pow2 n < pow2 m))
let lemma_pow2_lt n m = FStar.Math.Lemmas.pow2_lt_compat m n
    
val lemma_pow2_mul: n:nat -> m:nat -> Lemma
    (pow2 n * pow2 m = pow2 (n + m))
let lemma_pow2_mul n m = FStar.Math.Lemmas.pow2_plus n m

val lemma_pow2_mul_range: a:pos -> b:nat -> n:pos -> Lemma
    (requires (pow2 (n - 1) <= a /\ a < pow2 n))
    (ensures  (pow2 (n + b - 1) <= a * pow2 b /\ a * pow2 b < pow2 (n + b)))
let lemma_pow2_mul_range a b n =
    lemma_mul_le_right (pow2 b) (pow2 (n - 1)) a;
    lemma_pow2_mul (n - 1) b;
    lemma_mul_lt_right (pow2 b) a (pow2 n);
    lemma_pow2_mul n b
    
val lemma_pow2_small_div: n:nat -> m:nat -> Lemma
    (requires (n < m))
    (ensures  (pow2 n / pow2 m = 0))
let lemma_pow2_small_div n m =
    lemma_pow2_lt n m;
    lemma_small_div (pow2 n) (pow2 m)

val lemma_pow2_small_mod: n:nat -> m:nat -> Lemma
    (requires (n < m))
    (ensures  (pow2 n % pow2 m = pow2 n))
let lemma_pow2_small_mod n m =
    lemma_pow2_lt n m;
    lemma_small_mod  (pow2 n) (pow2 m)

val lemma_pow2_div: n:nat -> m:nat -> Lemma
    (requires (m <= n))
    (ensures  (pow2 n / pow2 m = pow2 (n - m)))
let lemma_pow2_div n m = FStar.Math.Lemmas.pow2_minus n m

val lemma_pow2_mod: n:nat -> m:nat -> Lemma
    (requires (m <= n))
    (ensures  (pow2 n % pow2 m = 0))
let lemma_pow2_mod n m = 
    lemma_pow2_mul (n - m) m;
    lemma_multiple_mod (pow2 (n - m)) (pow2 m)

val lemma_pow2_double: n:nat -> Lemma
    (pow2 n + pow2 n = pow2 (n + 1))
let lemma_pow2_double n = ()

val lemma_pow2_div_lt: a:nat -> b:nat -> d:nat -> Lemma
    (requires (a < pow2 b /\ d <= b))
    (ensures  (a / pow2 d < pow2 (b - d)))
let lemma_pow2_div_lt a b d = 
    lemma_pow2_div b d;
    lemma_pow2_mod b d;
    lemma_div_lt a (pow2 b) (pow2 d)
    
val lemma_pow2_div_range: a:pos -> b:nat -> n:pos -> Lemma
    (requires (n > b /\ pow2 (n - 1) <= a /\ a < pow2 n))
    (ensures  (pow2 (n - b - 1) <= a / pow2 b /\ a / pow2 b < pow2 (n - b)))
let lemma_pow2_div_range a b n =
    lemma_div_le (pow2 (n - 1)) a (pow2 b);
    lemma_pow2_div (n - 1) b;
    lemma_pow2_div_lt a n b
    
val lemma_pow2_multiple_le: a:nat -> b:nat -> d:nat -> Lemma
    (requires (a < pow2 b /\ d <= b /\ a % pow2 d = 0))
    (ensures  (a + pow2 d <= pow2 b))
let lemma_pow2_multiple_le a b d =
    lemma_pow2_div_lt a b d;
    lemma_distr_sub_left (pow2 (b - d)) 1 (pow2 d);
    lemma_pow2_mul (b - d) d

val lemma_pow2_div_div: a:nat -> b:nat -> c:nat -> Lemma
    ((a / pow2 b) / pow2 c = a / pow2 (b + c))
let lemma_pow2_div_div a b c =
    lemma_pow2_mul b c;
    lemma_div_div a (pow2 b) (pow2 c)

val lemma_pow2_mod_div: a:nat -> b:nat -> c:nat -> Lemma
    (requires (b >= c))
    (ensures  ((a % pow2 b) / pow2 c = (a / pow2 c) % (pow2 (b - c))))
let lemma_pow2_mod_div a b c =
    lemma_pow2_mul c (b - c);
    lemma_mod_div a (pow2 c) (pow2 (b - c))

val lemma_pow2_mod_mod: a:nat -> b:nat -> c:nat -> Lemma
    (requires (b >= c))
    (ensures  ((a % pow2 b) % pow2 c = a % pow2 c))
let lemma_pow2_mod_mod a b c =
    lemma_pow2_mul c (b - c);
    lemma_mod_mod a (pow2 c) (pow2 (b - c))
