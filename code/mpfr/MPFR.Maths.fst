module MPFR.Maths

open FStar.Mul

#set-options "--z3refresh --z3rlimit 5 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* Comment line which starts with "//!" explains the idea of proving *)

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

(* Function log2 *)
val log2: a:pos -> n:nat{pow2 n <= a /\ a < pow2 (n + 1)}
let rec log2 a = if a = 1 then 0 else log2 (a / 2) + 1

val lemma_log2_pow2: n:nat -> Lemma 
    (ensures (log2 (pow2 n) = n))
    [SMTPat (log2 (pow2 n))]
let rec lemma_log2_pow2 n = if n = 0 then () else lemma_log2_pow2 (n - 1)

val lemma_log2_le: a:pos -> b:pos -> Lemma
    (requires (a <= b))
    (ensures  (log2 a <= log2 b))
let rec lemma_log2_le a b = if a = 1 then () else lemma_log2_le (a / 2) (b / 2)

val lemma_log2_lt: a:pos -> b:nat -> Lemma
    (requires (a < pow2 b))
    (ensures  (log2 a < b))
let rec lemma_log2_lt a b = if a < 2 then () else lemma_log2_lt (a / 2) (b - 1)

val lemma_log2_lt_inv: a:pos -> b:pos -> Lemma
    (requires (log2 a < log2 b))
    (ensures  (a < b))
    [SMTPat (log2 a < log2 b)]
let lemma_log2_lt_inv a b = if a < b then () else lemma_log2_le b a

val lemma_log2_mul: a:pos -> b:nat -> Lemma
    (ensures (log2 (a * pow2 b) = log2 a + b))
    [SMTPat (log2 (a * pow2 b))]
let rec lemma_log2_mul a b = 
    if b = 0 then () else begin
        lemma_pow2_div b 1;
	lemma_mul_div (pow2 b) a 2;
        lemma_log2_mul a (b - 1)
    end

val lemma_log2_div: a:pos -> b:nat -> Lemma
    (requires (log2 a >= b))
    (ensures  (a / pow2 b > 0 /\ log2 (a / pow2 b) = log2 a - b))
    [SMTPat (log2 (a / pow2 b))]
let rec lemma_log2_div a b =
    if b = 0 then () else begin
        lemma_pow2_div b 1;
	lemma_pow2_div_div a (b - 1) 1;
        lemma_log2_div a (b - 1)
    end
    

(* Lemmas about bitwise operations *)
open FStar.BitVector
open FStar.UInt
open FStar.UInt64

type u64 = FStar.UInt64.t

val lemma_ge_pow2_imp_fst_bit: x:u64 -> Lemma
    (requires (v x >= pow2 63))
    (ensures  (nth (v x) 0 = true))
let lemma_ge_pow2_imp_fst_bit x = admit()

val lemma_fst_bit_imp_ge_pow2: x:u64 -> Lemma
    (requires (nth (v x) 0 = true))
    (ensures  (v x >= pow2 63))
let lemma_fst_bit_imp_ge_pow2 x = admit()

val lemma_tl_zero_imp_mod_pow2: x:u64 -> sh:nat{sh <= 64} -> Lemma
    (requires (forall (i:nat{64 - sh <= i /\ i < 64}). nth (v x) i = false))
    (ensures  (v x % pow2 sh = 0))
let lemma_tl_zero_imp_mod_pow2 x sh = admit()

val lemma_mod_pow2_imp_tl_zero: x:u64 -> sh:nat{sh <= 64} -> Lemma
    (requires (v x % pow2 sh = 0))
    (ensures  (forall (i:nat{64 - sh <= i /\ i < 64}). nth (v x) i = false))
let lemma_mod_pow2_imp_tl_zero x sh = admit()

val lemma_logor_disjoint: a:u64 -> b:u64 -> p:pos{p < 64} -> Lemma
    (requires (v a % pow2 p = 0 /\ v b < pow2 p))
    (ensures  (v (a |^ b) = v a + v b))
let lemma_logor_disjoint a b p = logor_disjoint (v a) (v b) p

val lemma_xor_and_distr: a:u64 -> b:u64 -> c:u64 -> Lemma
    (v ((a &^ b) ^^ (a &^ c)) = v (a &^ (b ^^ c)))
let lemma_xor_and_distr a b c =
    nth_lemma (UInt.logand (v a) (UInt.logxor (v b) (v c))) 
              (UInt.logxor (UInt.logand (v a) (v b)) (UInt.logand (v a) (v c)))

val lemma_bit_mask: mask:u64 -> p:nat{p < 64} -> Lemma
    (requires (v mask = pow2 (63 - p)))
    (ensures  (forall (i:nat{0 <= i /\ i < 64}). (i = p ==> nth (v mask) i = true) /\
                                        (i <> p ==> nth (v mask) i = false)))
let lemma_bit_mask mask p = 
    lemma_pow2_lt (63 - p) 64;
    nth_lemma (v mask) (UInt.shift_left (one 64) (63 - p))

val lemma_tail_mask: mask:u64 -> p:pos{p <= 64} -> Lemma
    (requires (v mask = pow2 p - 1))
    (ensures  (forall (i:nat{0 <= i /\ i < 64}). (i < 64 - p ==> nth (v mask) i = false) /\
                                        (i >= 64 - p ==> nth (v mask) i = true)))
let lemma_tail_mask mask p = lemma_pow2_le p p

val lemma_bit_mask_value: a:u64 -> mask:u64 -> p:nat{p < 64} -> Lemma
    (requires (v mask = pow2 (63 - p)))
    (ensures  (v (a &^ mask) = (if nth (v a) p then v mask else 0)))
let lemma_bit_mask_value a mask p =
    assert(v mask = pow2_n #64 (63 - p));
    if nth (v a) p then nth_lemma (UInt.logand (v a) (v mask)) (v mask)
    else nth_lemma (UInt.logand (v a) (v mask)) (zero 64)

val lemma_tail_mask_value: a:u64 -> mask:u64 -> p:nat{p < 64} -> Lemma
    (requires (v mask = pow2 p - 1))
    (ensures  (v (a &^ mask) = v a % pow2 p))
let lemma_tail_mask_value a mask p = 
    if p > 0 then logand_mask (v a) p else begin
        assert(v mask = zero 64);
	nth_lemma (v (a &^ mask)) (zero 64)
    end
