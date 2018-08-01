module MPFR.Maths

open FStar.Mul

#set-options "--z3refresh --z3rlimit 30 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* Nonlinear arithmetic *)
val lemma_paren_mul_left: a:int -> b:int -> c:int -> Lemma
    (a * b * c = (a * b) * c)
let lemma_paren_mul_left a b c = ()

val lemma_paren_mul_right: a:int -> b:int -> c:int -> Lemma
    (a * b * c = a * (b * c))
let lemma_paren_mul_right a b c = ()

val lemma_mul_zero: a:int -> b:pos -> Lemma
    (a = 0 <==> a * b = 0)
let lemma_mul_zero a b = ()

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
let lemma_add_div a n d =
    assert(a / d + n - 1 < (a + n * d) / d /\ (a + n * d) / d < a / d + n + 1)

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

val lemma_multiple_le: a:nat -> b:nat -> d:pos -> Lemma
    (requires (a < b /\ a % d = 0 /\ b % d = 0))
    (ensures  (a + d <= b))
let lemma_multiple_le a b d =
    lemma_div_lt a b d;
    lemma_distr_add_left (a / d) 1 d

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

val lemma_mod_distr_sub: a:nat -> b:nat -> c:pos -> Lemma
    (requires (a >= b))
    (ensures  ((a - b) % c = (a % c - b % c + c) % c))

let lemma_mod_distr_sub a b c =
    lemma_euclidean a c;
    //! assert((a - b) / c = ((a / c - b / c - 1) * c + (a % c - b % c + c)) / c);
    lemma_add_mod (a % c - b % c + c) (a / c - b / c - 1) c

val lemma_mod_distr_sub_zero: a:nat -> b:nat -> c:pos -> Lemma
    (requires (a % c = 0 /\ b % c = 0 /\ a >= b))
    (ensures  ((a - b) % c = 0))

let lemma_mod_distr_sub_zero a b c = lemma_mod_distr_sub a b c

val lemma_div_mul: a:nat -> b:pos -> Lemma
    (requires (a % b = 0))
    (ensures  ((a / b) * b = a))

let lemma_div_mul a b = ()

val lemma_div_div: a:nat -> b:pos -> c:pos -> Lemma
    ((a / b) / c = a / (b * c))
    
let lemma_div_div a b c =
    let adb = a / b in
    lemma_euclidean a b;
    //! assert(a = adb * b + a % b);
    lemma_euclidean adb c;
    //! assert(adb = (adb / c) * c + adb % c);
    lemma_distr_add_left b ((adb / c) * c) (adb % c);
    //! assert(a = ((adb % c) * b + a % b) + ((adb / c) * (b * c)));
    lemma_add_div ((adb % c) * b + a % b) (adb / c) (b * c);
    //! assert(a / (b * c) = adb / c + ((adb % c) * b + a % b) / (b * c));
    lemma_mul_le_right b (adb % c) (c - 1);
    //! assert((adb % c) * b <= (c - 1) * b);
    //! assert((adb % c) * b + a % b <= (c - 1) * b + (b - 1));
    lemma_distr_sub_left c 1 b;
    lemma_small_div (((a / b) % c) * b + a % b) (b * c);
    assert(a / (b * c) = adb / c)
    
val lemma_div_mod: a:nat -> b:pos -> c:pos -> Lemma 
    ((a / b) % c = (a % (b * c)) / b)
    
let lemma_div_mod a b c =
    lemma_euclidean a (b * c);
    //! assert(a = (a / (b * c)) * (b * c) + a % (b * c));
    lemma_add_div a (- (a / (b * c)) * c) b;
    //! assert((a % (b * c)) / b = a / b - (a / (b * c)) * c);
    lemma_div_div a b c;
    //! assert((a % (b * c)) / b = a / b - ((a / b) / c) * c);
    lemma_euclidean (a / b) c;
    assert((a / b) % c = (a % (b * c)) / b)

val lemma_mul_div: a:nat -> b:nat -> c:pos -> Lemma
    (requires (b % c = 0))
    (ensures  ((a * b) / c = a * (b / c)))
    
let lemma_mul_div a b c =
    lemma_euclidean b c;
    //! assert((a * b) / c = (a * (b / c) * c + a * (b % c)) / c);
    lemma_multiple_div (a * (b / c)) c

val lemma_mul_mod_zero: a:nat -> b:nat -> c:pos -> Lemma
    (requires (a % c = 0 \/ b % c = 0))
    (ensures  ((a * b) % c = 0))
    (decreases (b % c))

let rec lemma_mul_mod_zero a b c =
    if b % c > 0 then lemma_mul_mod_zero b a c else lemma_multiple_mod (a * (b / c)) c

val lemma_mod_mod: a:nat -> b:pos -> c:pos -> Lemma
    ((a % (b * c)) % b = a % b)
    
let lemma_mod_mod a b c =
    lemma_euclidean a (b * c);
    lemma_add_mod a (- (a / (b * c)) * c) b

val lemma_mod_mul: a:nat -> b:pos -> c:pos -> Lemma
    ((a % b) * c = (a * c) % (b * c))

let lemma_mod_mul a b c =
    lemma_div_mod (a * c) c b;
    lemma_multiple_div a c;
    //! assert((a * c) % (c * b) / c = a % b);
    lemma_mod_mod (a * c) c b;
    //! assert((a * c) % (c * b) % c = (a * c) % c);
    lemma_multiple_mod a c;
    lemma_div_mul ((a * c) % (c * b)) c

val lemma_mod_product_zero: a:nat -> b:nat -> c:pos -> d:pos -> Lemma
    (requires (a % c = 0 /\ b % d = 0))
    (ensures  ((a * b) % (c * d) = 0))

let lemma_mod_product_zero a b c d = 
    lemma_mod_mul (a * (b / d)) c d;
    //! assert((a * (b / d) % c) * d = (a * b) % (c * d));
    lemma_mul_mod_zero a (b / d) c


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
    lemma_pow2_mod b d;
    lemma_multiple_le a (pow2 b) (pow2 d)

val lemma_pow2_div_mul: a:nat -> b:nat -> c:nat -> Lemma
    (requires (a % pow2 b = 0 /\ b <= c))
    (ensures  ((a / pow2 b) * pow2 c = a * pow2 (c - b)))
    
let lemma_pow2_div_mul a b c = 
    lemma_pow2_mul b (c - b);
    lemma_div_mul a (pow2 b)

val lemma_pow2_div_div: a:nat -> b:nat -> c:nat -> Lemma
    ((a / pow2 b) / pow2 c = a / pow2 (b + c))
    
let lemma_pow2_div_div a b c =
    lemma_pow2_mul b c;
    lemma_div_div a (pow2 b) (pow2 c)

val lemma_pow2_mul_div: a:nat -> b:nat -> c:nat -> Lemma
    (requires (b <= c))
    (ensures  ((a * pow2 b) / pow2 c = a / pow2 (c - b)))

let lemma_pow2_mul_div a b c =
    lemma_pow2_div_div (a * pow2 b) b (c - b);
    lemma_multiple_div a (pow2 b)

val lemma_pow2_mul_mod: a:nat -> b:nat -> c:nat -> Lemma
    (requires (b <= c))
    (ensures  ((a * pow2 b) % pow2 c = (a % pow2 (c - b)) * pow2 b))

let lemma_pow2_mul_mod a b c = 
    lemma_mod_mul a (pow2 (c - b)) (pow2 b);
    lemma_pow2_mul (c - b) b

val lemma_pow2_mod_div: a:nat -> b:nat -> c:nat -> Lemma
    (requires (b >= c))
    (ensures  ((a % pow2 b) / pow2 c = (a / pow2 c) % (pow2 (b - c))))
    
let lemma_pow2_mod_div a b c =
    lemma_pow2_mul c (b - c);
    lemma_div_mod a (pow2 c) (pow2 (b - c))

val lemma_pow2_mod_mod: a:nat -> b:nat -> c:nat -> Lemma
    (requires (b >= c))
    (ensures  ((a % pow2 b) % pow2 c = a % pow2 c))
    
let lemma_pow2_mod_mod a b c =
    lemma_pow2_mul c (b - c);
    lemma_mod_mod a (pow2 c) (pow2 (b - c))

val lemma_pow2_mod_mod_zero: a:nat -> b:nat -> c:nat -> Lemma
    (requires (a % pow2 b = 0 /\ b >= c))
    (ensures  (a % pow2 c = 0))
    
let lemma_pow2_mod_mod_zero a b c = lemma_pow2_mod_mod a b c

val lemma_pow2_mod_product_zero: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
    (requires (a % pow2 c = 0 /\ b % pow2 d = 0))
    (ensures  ((a * b) % pow2 (c + d) = 0))

let lemma_pow2_mod_product_zero a b c d =
    lemma_pow2_mul c d;
    lemma_mod_product_zero a b (pow2 c) (pow2 d)

val lemma_bit_length: m:pos -> p1:pos -> p2:pos -> Lemma
    (requires (pow2 (p1 - 1) <= m /\ m < pow2 p1 /\ pow2 (p2 - 1) <= m /\ m < pow2 p2))
    (ensures  (p1 = p2))

let lemma_bit_length m p1 p2 =
    if p1 < p2 then lemma_pow2_le p1 (p2 - 1);
    if p1 > p2 then lemma_pow2_le p2 (p1 - 1)

(* Bitwise lemmas *)
open FStar.Seq
open FStar.UInt
open FStar.BitVector

val lemma_nth_logand: #n:pos -> a:uint_t n -> i:nat{i < n} -> Lemma
    (requires (pow2 (n - i - 1) < pow2 n))
    (ensures  (nth a i = (logand a (pow2 (n - i - 1)) <> 0)))
    
let lemma_nth_logand #n a i = 
    lemma_pow2_lt (n - i - 1) n;
    nth_lemma (pow2 (n - i - 1)) (shift_left (one n) (n - i - 1));
    if nth a i then nth_lemma (logand a (pow2 (n - i - 1))) (pow2 (n - i - 1))
    else nth_lemma (logand a (pow2 (n - i - 1))) (zero n)

val slice_left_nth_lemma: #n:pos -> a:uint_t n -> m:pos{m <= n} -> Lemma
    (forall (i:nat{i < m}). (lemma_pow2_div_lt a n (n - m); nth a i = nth #m (a / pow2 (n - m)) i))

let slice_left_nth_lemma #n a m = if n = m then () else slice_left_lemma (to_vec a) m

val slice_right_nth_lemma: #n:pos -> a:uint_t n -> m:pos{m <= n} -> Lemma
    (forall (i:nat{i < m}). nth a (n - m + i) = nth #m (a % pow2 m) i)

let slice_right_nth_lemma #n a m = if n = m then () else slice_right_lemma (to_vec a) m

val lemma_logor_disjoint: #n:pos -> a:uint_t n -> b:uint_t n -> Lemma
    (requires (forall (i:nat{i < n}). nth a i ==> not (nth b i)))
    (ensures  (logor a b = a + b))

let rec lemma_logor_disjoint #n a b =
    if n = 1 then begin
        if nth b 0 = false then () else assert(nth a 0 = false)
    end else begin
        slice_left_nth_lemma a (n - 1);
        slice_left_nth_lemma b (n - 1);
        slice_left_nth_lemma (logor a b) (n - 1);
        slice_right_nth_lemma a 1;
        slice_right_nth_lemma b 1;
        slice_right_nth_lemma (logor a b) 1;
	lemma_pow2_div_lt a n 1;
	lemma_pow2_div_lt b n 1;
	lemma_logor_disjoint #(n - 1) (a / 2) (b / 2);
	lemma_logor_disjoint #1 (a % 2) (b % 2);
	nth_lemma (logor a b) (a + b)
    end

val lemma_xor_and_distr: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n -> Lemma
    (logxor (logand a b) (logand a c) = logand a (logxor b c))
let lemma_xor_and_distr #n a b c =
    nth_lemma (logxor (logand a b) (logand a c)) (logand a (logxor b c))

val lemma_hd_zero_imp_lt_pow2: #n:pos -> x:uint_t n -> sh:nat{sh <= n} -> Lemma
    (requires (forall (i:nat{i < sh}). nth x i = false))
    (ensures  (x < pow2 (n - sh)))
let lemma_hd_zero_imp_lt_pow2 #n x sh =
    if sh = 0 then () else if sh = n then nth_lemma x (zero n) else begin
        assert(forall (i:nat{i < sh}). index (to_vec x) i = false);
        lemma_eq_intro (slice (to_vec x) 0 sh) (zero_vec #sh);
        slice_left_lemma (to_vec x) sh
    end

val lemma_lt_pow2_imp_hd_zero: #n:pos -> x:uint_t n -> sh:nat{sh <= n} -> Lemma
    (requires (x < pow2 (n - sh)))
    (ensures  (forall (i:nat{i < sh}). nth x i = false))
let lemma_lt_pow2_imp_hd_zero #n x sh =
    if sh = 0 then () else if sh = n then nth_lemma x (zero n) else begin
        slice_left_lemma (to_vec x) sh;
        lemma_eq_intro (slice (to_vec x) 0 sh) (to_vec (zero sh));
	assert(forall (i:nat{i < sh}). index (to_vec x) i = index (slice (to_vec x) 0 sh) i)
    end
    
val lemma_tl_zero_imp_mod_pow2: #n:pos -> x:uint_t n -> sh:nat{sh <= n} -> Lemma
    (requires (forall (i:nat{n - sh <= i /\ i < n}). nth x i = false))
    (ensures  (x % pow2 sh = 0))
let lemma_tl_zero_imp_mod_pow2 #n x sh =
    if sh = 0 then () else if sh = n then nth_lemma x (zero n) else begin
        assert(forall (i:nat{n - sh <= i /\ i < n}). index (to_vec x) i = false);
        lemma_eq_intro (slice (to_vec x) (n - sh) n) (zero_vec #sh);
        slice_right_lemma (to_vec x) sh
    end

val lemma_mod_pow2_imp_tl_zero: #n:pos -> x:uint_t n -> sh:nat{sh <= n} -> Lemma
    (requires (x % pow2 sh = 0))
    (ensures  (forall (i:nat{n - sh <= i /\ i < n}). nth x i = false))
let lemma_mod_pow2_imp_tl_zero #n x sh =
    if sh = 0 then () else if sh = n then nth_lemma x (zero n) else begin
        slice_right_lemma (to_vec x) sh;
        lemma_eq_intro (slice (to_vec x) (n - sh) n) (to_vec (zero sh));
	assert(forall (i:nat{n - sh <= i /\ i < n}). index (to_vec x) i = index (slice (to_vec x) (n - sh) n) (i + sh - n))
    end

(* UInt64 lemmas *)
open FStar.UInt64

type u64 = FStar.UInt64.t

val lemma_logor_pow2_disjoint: a:u64 -> b:u64 -> p:pos{p < 64} -> Lemma
    (requires (v a % pow2 p = 0 /\ v b < pow2 p))
    (ensures  (v (a |^ b) = v a + v b))
let lemma_logor_pow2_disjoint a b p = 
    lemma_mod_pow2_imp_tl_zero (v a) p;
    lemma_lt_pow2_imp_hd_zero (v b) (64 - p);
    lemma_logor_disjoint (v a) (v b)

val lemma_lognot_value: a:u64 -> Lemma
    (v (lognot a) = pow2 64 - 1 - v a)
let lemma_lognot_value a =
    lemma_logor_disjoint (v (lognot a)) (v a);
    lemma_eq_intro (logor_vec (to_vec (v (lognot a))) (to_vec (v a))) (ones_vec #64)

val lemma_lognot_mask_mod: a:u64 -> mask:u64 -> sh:nat{sh < 64} -> Lemma
    (requires (v mask = pow2 sh - 1))
    (ensures  (v (a &^ (lognot mask)) % pow2 sh = 0))
let lemma_lognot_mask_mod a mask sh =
    lemma_lognot_value mask;
    lemma_pow2_mod 64 sh;
    lemma_pow2_lt sh 64;
    lemma_mod_distr_sub_zero (pow2 64) (pow2 sh) (pow2 sh);
    if sh = 0 then () else begin
        lemma_mod_pow2_imp_tl_zero (v (lognot mask)) sh;
        lemma_eq_intro (slice (to_vec (v (a &^ (lognot mask)))) (64 - sh) 64) (zero_vec #sh);
	lemma_tl_zero_imp_mod_pow2 (v (a &^ (lognot mask))) sh
    end
    
val lemma_bit_mask: mask:u64 -> p:nat{p < 64} -> Lemma
    (requires (v mask = pow2 (63 - p)))
    (ensures  (forall (i:nat{0 <= i /\ i < 64}). (i = p ==> nth (v mask) i = true) /\
                                        (i <> p ==> nth (v mask) i = false)))
let lemma_bit_mask mask p = 
    lemma_pow2_lt (63 - p) 64;
    nth_lemma (v mask) (UInt.shift_left (one 64) (63 - p))
    
val lemma_bit_mask_value: a:u64 -> mask:u64 -> p:nat{p < 64} -> Lemma
    (requires (v mask = pow2 (n - p - 1)))
    (ensures  (v (a &^ mask) = (if nth (v a) p then v mask else 0)))
let lemma_bit_mask_value a mask p =
    assert(v mask = pow2_n #n (n - p - 1));
    if nth (v a) p then nth_lemma (v (a &^ mask)) (v mask)
    else nth_lemma (v (a &^ mask)) (zero n)
    
val lemma_tail_mask: mask:u64 -> p:pos{p <= 64} -> Lemma
    (requires (v mask = pow2 p - 1))
    (ensures  (forall (i:nat{0 <= i /\ i < 64}). (i < 64 - p ==> nth (v mask) i = false) /\
                                        (i >= 64 - p ==> nth (v mask) i = true)))
let lemma_tail_mask mask p = lemma_pow2_le p p

val lemma_tail_mask_value: a:u64 -> mask:u64 -> p:nat{p < 64} -> Lemma
    (requires (v mask = pow2 p - 1))
    (ensures  (v (a &^ mask) = v a % pow2 p))
let lemma_tail_mask_value a mask p = 
    if p > 0 then logand_mask (v a) p else begin
        assert(v mask = zero 64);
	nth_lemma (v (a &^ mask)) (zero 64)
    end

val lemma_sb_logor: #n:pos -> x:uint_t n -> a:pos{a < n} -> b:pos{b <= a} -> sb1:u64 -> sb2:u64 -> Lemma
    (requires ((x % pow2 b <> 0) = (v sb1 <> 0) /\ ((x / pow2 b) % pow2 (a - b) <> 0) = (v sb2 <> 0)))
    (ensures  ((x % pow2 a <> 0) = (v (sb1 |^ sb2) <> 0)))

let lemma_sb_logor #n x a b sb1 sb2 =
    lemma_pow2_mod_div x a b;
    lemma_pow2_mod_mod x a b;
    lemma_euclidean x (pow2 b);
    if v sb1 = 0 && v sb2 = 0 then nth_lemma (v (sb1 |^ sb2)) (zero 64)
    else logor_ge (v sb1) (v sb2)
