module Hacl.Spec.P256.Lemmas

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Hacl.Spec.P256.Basic

open FStar.Mul

open Hacl.Spec.P256.Definitions


#reset-options " --z3rlimit 100" 

noextract
val log_and: a: uint64 -> b: uint64{uint_v b == 0 \/ uint_v b == pow2 64 - 1} -> 
Lemma (if uint_v b = 0 then uint_v (logand a b) == 0 else uint_v (logand a b) == uint_v a)

let log_and a b = 
  logand_lemma b a;
  logand_spec a b;
  logand_spec b a;
  UInt.logand_commutative #(bits U64) (v a) (v b)

noextract
val log_or: a: uint64 -> b: uint64 {uint_v b == 0 \/ uint_v a == 0} -> 
Lemma (if uint_v b = 0 then uint_v (logor a b) == uint_v a else uint_v (logor a b) == uint_v b)

noextract
val log_not_lemma: b: uint64{uint_v b == 0 \/ uint_v b == pow2 64 - 1} -> 
Lemma(if uint_v b = 0 then uint_v (lognot (b)) == pow2 64 -1 else uint_v (lognot b) == 0)

let log_or a b = admit()
let log_not_lemma a = admit()



noextract
val lemma_nat_4: f: felem4 -> Lemma (as_nat4 f < pow2 256)

let lemma_nat_4 f = 
  let (s0, s1, s2, s3) = f in 
  let r_n = as_nat4 f in 
  let r = uint_v s0 + uint_v s1 * pow2 64 + uint_v s2 * pow2 64 * pow2 64 + 
  uint_v s3 * pow2 64 * pow2 64 * pow2 64 in 
  assert(r_n == r);
  assert_norm(r < pow2 256)


noextract
val lemma_enough_to_carry: a: felem4 -> b: felem4 -> Lemma (
  if as_nat4 b >= (pow2 256 - as_nat4 a) then 
    let (c, r) = add4 a b in 
    uint_v c == 1
    else True)
    
let lemma_enough_to_carry a b = 
 if as_nat4 b >= (pow2 256 - as_nat4 a) then begin
  let (c, r) = add4 a b in 
    lemma_nat_4 r
  end
  else
  ()

#reset-options " --z3rlimit 100" 


noextract   
let ( +% ) a b = (a + b) % prime256
noextract
let ( -% ) a b = (a - b) % prime256
noextract
let ( *% ) a b prime = (a * b) % prime

noextract
let rec exp (e: nat) (n:nat {n > 0}) (prime: pos) : Tot (r: nat) (decreases n)  =
  let ( *%) a b =  ( *% ) a b prime in 

  if n = 1 then e
  else
    if n % 2 = 0 then 
    begin
      exp (e *% e) (n/2) prime
    end
    else e *% (exp (e *% e)((n-1)/2) prime)


noextract 
let modp_inv_prime (prime: pos {prime > 3}) (x: nat {x < prime})  : Tot (r: nat{r < prime}) = 
  (exp x (prime - 2) prime) % prime

noextract
let modp_inv2_prime (x: int) (p: nat {p > 3}) : Tot (r: nat {r < p}) = 
  assert_norm (p > 0);
  let r:nat = x % p in  
  modp_inv_prime p r

noextract
let modp_inv (x: nat {x < prime256}) : Tot (r: nat{r < prime256}) = 
  assert_norm (prime256 > 3);
  modp_inv_prime prime256 x

noextract
let modp_inv2 (x: nat) : Tot (r: nat {r < prime256}) = 
  assert_norm (prime256 > 3);
  modp_inv2_prime x prime256


noextract
val modulo_distributivity_mult: a: int -> b: int -> c: pos -> Lemma ((a * b) % c = ((a % c) * (b % c)) % c)

let modulo_distributivity_mult a b c = 
  lemma_mod_mul_distr_l a b c;
  lemma_mod_mul_distr_r (a%c) b c

val power_one: a: nat -> Lemma (pow 1 a == 1) 

let rec power_one a = 
  match a with 
  | 0 -> assert_norm (pow 1 0 == 1)
  | _ -> power_one (a - 1);
    assert(pow 1 (a - 1) == 1)


noextract
val pow_plus: a: nat -> b: nat -> c: nat -> Lemma (ensures (pow a b * pow a c = pow a (b +c)))
(decreases b)

let rec pow_plus a b c = 
  match b with 
  | 0 -> assert_norm (pow a 0 = 1)
  | _ -> pow_plus a (b -1) c; 
    assert_norm(pow a (b - 1) * a = pow a b)


noextract
val power_distributivity: a: nat -> b: nat -> c: pos -> Lemma ((pow (a % c) b) % c = (pow a b) % c)

let rec power_distributivity a b c =
   match b with 
   | 0 -> ()
   | _ -> 
     power_distributivity a (b - 1) c; 
     modulo_distributivity_mult (pow a (b -1)) a c;
     lemma_mod_twice a c;
     modulo_distributivity_mult (pow (a % c) (b -1)) (a % c) c

val lemma_power_one: a: nat -> Lemma (pow a 1 == a)

let lemma_power_one a = ()

noextract
val power_mult: a: nat -> b: nat -> c: nat -> Lemma (pow (pow a b) c == pow a (b * c))

let rec power_mult a b c = 
  match c with 
  |0 -> assert_norm(pow a 0 = 1); assert(pow (pow a b) 0  = 1)
  |_ ->  power_mult a b (c -1); pow_plus a (b * (c -1)) b



val power_distributivity_2: a: nat -> b: nat -> c: pos -> 
  Lemma (pow (a * b) c == pow a c * pow b c)

let rec power_distributivity_2 a b c = 
  match c with 
  |0 -> ()
  |1 -> ()
  | _ ->
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in
    power_distributivity_2 a b (c - 1);
    assert(pow (a * b) (c - 1) == pow a (c - 1) * pow b (c - 1));
    assert(pow (a * b) (c - 1) * pow (a * b) 1 == pow a (c - 1) * pow b (c - 1) * pow (a * b) 1);
    
    assert(pow (a * b) (c - 1) * pow (a * b) 1 == pow (a * b) c);
    assert(pow (a * b) 1 == a * b);
    assert(pow a (c - 1) * pow b (c - 1) * pow (a * b) 1 == pow a (c - 1) * pow b (c - 1) * a * b);
    assert_by_tactic (pow a (c - 1) * pow b (c - 1) * a * b == (pow a c * pow b c)) canon;
    assert(pow a (c - 1) * pow b (c - 1) * pow (a * b) 1 == (pow a c * pow b c));
    assert(pow a c * pow b c == pow (a * b) c)


val modulo_distributivity_mult_last_two: a: int -> b: int -> c: int -> d: int -> e: int -> f: pos -> 
Lemma ((a * b * c * d * e) % f = (a * b * c * ((d * e) % f)) % f)

let modulo_distributivity_mult_last_two a b c d e f = admit()


noextract
let modp_inv2_pow (x: nat) : Tot (r: nat {r < prime256}) = 
   power_distributivity x (prime256 - 2) prime256;
   pow x (prime256 - 2) % prime256
  


#reset-options "--max_fuel 0 --z3rlimit 100" 


val lemma_mod_twice : a:int -> p:pos -> Lemma ((a % p) % p == a % p)

let lemma_mod_twice a p = lemma_mod_mod (a % p) a p


val lemma_multiplication_to_same_number: a: nat -> b: nat ->c: nat -> prime: pos ->  
  Lemma (requires (a % prime = b % prime)) (ensures ((a * c) % prime = (b * c) % prime))


let lemma_multiplication_to_same_number a b c prime = 
  lemma_mod_mul_distr_l a c prime;
  lemma_mod_mul_distr_l b c prime


val lemma_division_is_multiplication: t3: nat{ exists (k: nat) . k * pow2 64 = t3} -> prime_: pos {prime_ > 3 /\
  (prime_ = 115792089210356248762697446949407573529996955224135760342422259061068512044369 \/ prime_ = prime256)} ->   
  Lemma (ensures (t3 * modp_inv2_prime (pow2 64) prime_  % prime_ = (t3 / pow2 64) % prime_))


let lemma_division_is_multiplication t3 prime_ =  
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  let remainder = t3 / pow2 64 in 
  (*
  SAGE: 
    prime = 2** 256 - 2** 224 + 2** 192 + 2** 96 -1
    inverse_mod ((2 ** 64), prime) * 2 ** 64 % prime
    1;

    prime = 115792089210356248762697446949407573529996955224135760342422259061068512044369
    inverse_mod ((2 ** 64), prime) * 2 ** 64 % prime
  
  *)
  assert_norm(prime256 > 3);
  let prime2 = 115792089210356248762697446949407573529996955224135760342422259061068512044369 in 
  assume(modp_inv2_prime (pow2 64) prime256 * pow2 64 % prime256 = 1); 
  assume(modp_inv2_prime (pow2 64) prime2 * pow2 64 % prime2 = 1);

  let k =  (modp_inv2_prime (pow2 64) prime_ * pow2 64) in 
  
  modulo_distributivity_mult remainder k prime_;
  assert((remainder * k) % prime_ = ((remainder % prime_)) % prime_);
  lemma_mod_twice remainder prime_;
    assert_by_tactic (t3 / pow2 64 * (modp_inv2_prime (pow2 64) prime_ * pow2 64) == t3/ pow2 64 * pow2 64 * modp_inv2_prime (pow2 64) prime_) canon;
  assert((t3 / pow2 64 * (modp_inv2_prime (pow2 64) prime_ * pow2 64)) % prime_ = remainder % prime_);
  assert((t3  * modp_inv2_prime (pow2 64) prime_) % prime_ = remainder % prime_)


#reset-options " --z3rlimit 300 --z3refresh" 


val lemma_reduce_mod_by_sub: t: nat -> Lemma
    ((t - t % pow2 64) % pow2 64 == 0)

let lemma_reduce_mod_by_sub t = ()


val lemma_multiplication_same_number2: a: int -> b: int -> c: int{a * b = c} -> d: int -> Lemma
    (a * b * d == c* d) 


let lemma_multiplication_same_number2 a b c d = ()


val lemma_add_mod: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> f: nat {f = a - b + c + d - e} -> k: pos -> 
  Lemma (
    f % k == ((a % k) - (b % k) + ( c % k) + (d % k) - (e % k)) % k)


let lemma_add_mod a b c d e f k = admit()



val lemma_reduce_mod_by_sub2: t: nat -> 
  Lemma ((prime256 * (t % pow2 64)) % pow2 64 == (-t)  % pow2 64)

let lemma_reduce_mod_by_sub2 t = 
  let t_ = t % pow2 64 in   
  let f = (pow2 256 - pow2 224 + pow2 192 + pow2 96 -1) * (t % pow2 64) in 
  assert(f == pow2 256 * t_ - pow2 224 * t_ + pow2 192 * t_ + pow2 96 * t_ - t_);
  lemma_add_mod (pow2 256 * t_) (pow2 224 * t_) (pow2 192 * t_) (pow2 96 * t_) t_ f (pow2 64);
  assert(f % (pow2 64) ==  ((pow2 256 * t_) % pow2 64 -  (pow2 224 * t_) % pow2 64 +  (pow2 192 * t_) % pow2 64 +  (pow2 96 * t_) % pow2 64 -  t_) % pow2 64);

    pow2_plus 192 64;
    lemma_multiplication_same_number2 (pow2 192) (pow2 64) (pow2 256) t_;
    multiple_modulo_lemma (pow2 192 * t_) (pow2 64);
    assert((pow2 256 * t_) % pow2 64 == 0);

    pow2_plus 160 64;
    lemma_multiplication_same_number2 (pow2 160) (pow2 64) (pow2 224) t_;
    multiple_modulo_lemma (pow2 160 * t_) (pow2 64);
    assert((pow2 224 * t_) % pow2 64 == 0);

    pow2_plus 128 64;
    lemma_multiplication_same_number2 (pow2 128) (pow2 64) (pow2 192) t_;
    multiple_modulo_lemma (pow2 128 * t_) (pow2 64);
    assert((pow2 192 * t_) % pow2 64 == 0);

    pow2_plus 32 64; 
    assert(pow2 32 * pow2 64 = pow2 96);

    lemma_multiplication_same_number2 (pow2 32) (pow2 64) (pow2 96) t_; 
    multiple_modulo_lemma (pow2 32 * t_) (pow2 64);
    assert((pow2 96 * t_) % pow2 64 == 0);

  assert(f % pow2 64 == (- (t % pow2 64)) % pow2 64);
  lemma_mod_sub_distr 0 t (pow2 64);
  assert(f % pow2 64 == (- t) % pow2 64)


val lemma_reduce_mod_by_sub3 : t: nat -> Lemma ((t + (t % pow2 64) * prime256) % pow2 64 == 0)

let lemma_reduce_mod_by_sub3 t = 
  lemma_reduce_mod_by_sub2 t


val mult_one_round: t: nat -> co: nat{t % prime256 == co% prime256}  -> Lemma
(let result = (t + (t % pow2 64) * prime256) / pow2 64 % prime256 in result == (co * modp_inv2 (pow2 64)) % prime256)


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
  t: nat -> k0: nat {k0 = modp_inv2_prime (-prime) (pow2 64)} ->  
  Lemma
    ((t + prime * (k0 * (t % pow2 64) % pow2 64)) % pow2 64 == 0)
    


let lemma_reduce_mod_ecdsa_prime prime t k0 = 
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 
  
  let f = prime * (k0 * (t % pow2 64) % pow2 64) in 
  let t0 = (t + f) % pow2 64 in 
  lemma_mod_add_distr t f (pow2 64);
  
  modulo_addition_lemma t (pow2 64) f;
  assert(t0 == (t + f % pow2 64) % pow2 64);
  lemma_mod_mul_distr_r k0 t (pow2 64);
    assert(k0 * (t % pow2 64) % pow2 64 = (k0 * t) % pow2 64);
  lemma_mod_mul_distr_r prime (k0 * t) (pow2 64);
    assert((prime * (k0 * (t % pow2 64) % pow2 64)) % pow2 64 == (prime * (k0 * t)) % pow2 64);
    assert_by_tactic(prime * (k0 * t) == (prime * k0) * t) canon;
    assert((prime * (k0 * (t % pow2 64) % pow2 64)) % pow2 64 == ((prime * k0) * t) % pow2 64);
    lemma_mod_mul_distr_l (prime * k0) t (pow2 64); 
      (*
       SAGE: 
       prime = 115792089210356248762697446949407573529996955224135760342422259061068512044369
       inverse_mod (- prime, 2 ** 64) * prime % 2 ** 64  == (-1) % 2** 64	*)
       assume((prime * k0) % pow2 64 == (-1) % pow2 64);  
    assert((prime * (k0 * (t % pow2 64) % pow2 64)) % pow2 64 == ((-1) % pow2 64 * t) % pow2 64);
    lemma_mod_mul_distr_l (-1) t (pow2 64);
    assert(f % pow2 64 == (-t) % pow2 64);

    assert((t + f) % pow2 64 == (t + (- t % pow2 64)) % pow2 64);
    lemma_mod_add_distr t (-t) (pow2 64);
    assert((t + f) % pow2 64 == 0)
  


val mult_one_round_ecdsa_prime: t: nat -> 
  prime: pos {prime = 115792089210356248762697446949407573529996955224135760342422259061068512044369} -> 
  co: nat {t % prime == co % prime} -> k0: nat {k0 = modp_inv2_prime (-prime) (pow2 64)} -> Lemma
  (let result = (t + prime * ((k0 * (t % pow2 64)) % pow2 64)) / pow2 64 in 
    result % prime == (co * modp_inv2_prime (pow2 64) prime) % prime)


let mult_one_round_ecdsa_prime t prime co k0 = 
  assert_norm (prime > 3);
  let t2 = ((k0 * (t % pow2 64)) % pow2 64) * prime in 
  let t3 = t + t2 in 
    modulo_addition_lemma t prime ((k0 * (t % pow2 64)) % pow2 64);
    assert(t3 % prime = co % prime);
    lemma_div_mod t3 (pow2 64);
    lemma_reduce_mod_ecdsa_prime prime t k0;
    assert(let rem = t3/ pow2 64 in rem * pow2 64 = t3);
    assert(exists (k: nat). k * pow2 64 = t3);
    lemma_division_is_multiplication t3 prime;
    lemma_multiplication_to_same_number t3 co (modp_inv2_prime (pow2 64) prime) prime


val lemma_decrease_pow: a: nat -> Lemma (ensures (a * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64))  % prime256 == (a * modp_inv2 (pow2 256)) % prime256) 


let lemma_decrease_pow a = 
  assert_norm(modp_inv2 (pow2 64) = 6277101733925179126845168871924920046849447032244165148672);
  assert_norm(pow2 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936);
  assert_norm(modp_inv2 (pow2 256) =115792089183396302114378112356516095823261736990586219612555396166510339686400 );
  assert((modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2(pow2 64))% prime256  = (modp_inv2 (pow2 256)) % prime256);

  lemma_mod_mul_distr_r a (modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2(pow2 64)) prime256;
  lemma_mod_mul_distr_r a (modp_inv2 (pow2 256)) prime256



val lemma_brackets : a: int -> b: int -> c: int -> Lemma (a * b * c = a * (b * c))

val lemma_brackets_l: a: int -> b: int -> c: int -> Lemma (a * b * c = (a * b) * c)


val lemma_brackets1: a: int -> b: int -> c: int -> Lemma (a * (b * c) = b * (a * c))


val lemma_brackets5: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (a * b * c * d * e = a * b * c * (d * e))


val lemma_brackets5_twice: a: int -> b: int -> c: int -> d: int -> e: int -> Lemma (a * b * c * d * e = (a * d) * (b * e) * c)


val lemma_brackets7: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> g: int -> Lemma (a * b * c * d * e * f * g = a * b * c * d * e * (f * g))



val lemma_brackets7_twice: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> g: int -> Lemma (a * b * c * d * e * f * g = (a * e) * (b * f) * (c * g) * d)




val lemma_distr_mult3: a: int -> b: int -> c: int -> Lemma (a * b * c = a * c * b)


val lemma_distr_mult : a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (a * b * c * d * e = a * b * d * c * e) 


val lemma_twice_brackets: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> h: int-> Lemma 
  ((a * b * c) * (d * e * f) * h = a * b * c * d * e * f * h)


val lemma_distr_mult7: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> h: int-> Lemma 
  ( a * b * c * d * e * f * h = a * b * d * e * f * h * c)


val lemma_prime_as_wild_nat: a: felem8{wide_as_nat4 a < 2* prime256} -> Lemma (let (t0, t1, t2, t3, t4, t5, t6, t7) = a in 
  uint_v t7 = 0 /\ uint_v t6 = 0 /\ uint_v t5 = 0 /\ (uint_v t4 = 0 \/ uint_v t4 = 1) /\
  as_nat4 (t0, t1, t2, t3) + uint_v t4 * pow2 256 = wide_as_nat4 a)


val lemma_mul_nat2: a: nat -> b: nat -> Lemma (a * b >= 0)


val lemma_mul_nat: a:nat -> b:nat -> c: nat -> Lemma (a * b * c >= 0)


val lemma_mul_nat4: a:nat -> b:nat -> c: nat -> d: nat -> Lemma (a * b * c * d >= 0)


val lemma_mul_nat5: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (a * b * c * d * e >= 0)

val modulo_distributivity_mult2: a: int -> b: int -> c: int -> d: pos -> Lemma (((a % d) * (b % d) * c) % d = (a * b * c)% d)

val lemma_minus_distr (a: int) (b: int): Lemma ((a % prime256 - b % prime256) % prime256 = (a - b)%prime256)


val lemma_multiplication_not_mod_prime: a: nat{a < prime256} -> b: nat {b > 0 /\ b % prime256 <> 0} -> 
  Lemma ((a * b) % prime256 == 0 <==> a == 0)

(*If k a ≡ k b (mod n) and k is coprime with n, then a ≡ b (mod n) *)

val lemma_modular_multiplication_p256: a: nat{a < prime256} -> b: nat{b < prime256} -> 
  Lemma 
  (a * modp_inv2 (pow2 256) % prime256 = b * modp_inv2 (pow2 256) % prime256  ==> a == b)


val lemma_mod_sub_distr (a:int) (b:int) (n:pos) : Lemma ((a - b % n) % n = (a - b) % n)


val lemma_mod_add_distr (a:int) (b:int) (n:pos) : Lemma ((a + b % n) % n = (a + b) % n)

val lemma_log_and1: a: uint64 {v a = 0 \/ v a = maxint U64} ->
  b: uint64 {v b = 0 \/ v b = maxint U64}  -> 
  Lemma (uint_v a = pow2 64 - 1 && uint_v b = pow2 64 - 1 <==> uint_v (logand a b) == pow2 64 - 1)

val lemma_xor_copy_cond: a: uint64 -> b: uint64 -> mask: uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 -1} ->
  Lemma(let r = logxor a (logand mask (logxor a b)) in 
  if uint_v mask = pow2 64 - 1 then r == b else r == a)


val lognot_lemma: #t:inttype{~(U1? t)} -> a:uint_t t SEC -> Lemma
  (requires v a = 0 \/ v a = maxint t)
  (ensures (if v a = 0 then v (lognot a) == maxint t else v (lognot a) == 0)) 


val lemma_equality: a: felem4 -> b: felem4 -> Lemma
    (
      let (a_0, a_1, a_2, a_3) = a in 
      let (b_0, b_1, b_2, b_3) = b in 

      if  (uint_v a_0 = uint_v b_0 && uint_v a_1 = uint_v b_1 && uint_v a_2 = uint_v b_2 && uint_v a_3 = uint_v b_3) then as_nat4 a == as_nat4 b else as_nat4 a <> as_nat4 b)

 val neq_mask_lemma: #t:inttype -> a:uint_t t SEC -> b:uint_t t SEC -> Lemma
  (requires True)
  (ensures  (v a <> v b ==> v (neq_mask a b) == maxint t) /\
            (v a == v b ==> v (neq_mask a b) == 0))


val cmovznz4_lemma: cin: uint64 -> x: uint64 -> y: uint64 -> Lemma (
  let mask = neq_mask cin (u64 0) in 
  let r = logor (logand y mask) (logand x (lognot mask)) in 
  if uint_v cin = 0 then uint_v r == uint_v x else uint_v r == uint_v y)


val lemma_equ_felem: a: nat{ a < pow2 64} -> b: nat {b < pow2 64} -> c: nat {c < pow2 64} -> d: nat {d < pow2 64} ->
   a1: nat{a1 < pow2 64} -> b1: nat {b1 < pow2 64} -> c1: nat {c1 < pow2 64} -> d1: nat {d1 < pow2 64} ->
  Lemma (requires (
    a + b * pow2 64 + c * pow2 64 * pow2 64 + d *  pow2 64 * pow2 64 * pow2 64 == 
    a1 + b1 * pow2 64 + c1 * pow2 64 * pow2 64  + d1 *  pow2 64 * pow2 64 * pow2 64))
  (ensures (a == a1 /\ b == b1 /\ c == c1 /\ d == d1))

val lemma_eq_funct: a: felem_seq -> b: felem_seq -> Lemma
   (requires (felem_seq_as_nat a == felem_seq_as_nat b))
   (ensures (a == b))


let lemma_brackets a b c = ()


let lemma_brackets_l a b c = ()


let lemma_brackets1 a b c = ()


let lemma_brackets5 a b c d e = ()


let lemma_brackets5_twice a b c d e = admit()


let lemma_brackets7 a b c d e f g = admit()


let lemma_brackets7_twice a b c d e f g = admit()



let lemma_distr_mult3 a b c = ()

let lemma_distr_mult a b c d e = ()


let lemma_twice_brackets a b c d e f h = () 

let lemma_distr_mult7 a b c d e f h = admit()


let lemma_prime_as_wild_nat a =
   assert_norm(pow2 64 * pow2 64 = pow2 128);
   assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
   assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 320);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64))
  

let lemma_mul_nat2 a b = ()

let lemma_mul_nat a b c = ()
let lemma_mul_nat4 a b c d = ()

let lemma_mul_nat5 a b c d e = ()


let modulo_distributivity_mult2 a b c d = 
  let start = ((a % d) * (b % d) * c) % d in 
  lemma_mod_mul_distr_l a ((b % d) * c) d;
  lemma_distr_mult3 a (b % d) c;
  lemma_mod_mul_distr_r (a * c) b d

let lemma_minus_distr a d = admit()


let lemma_multiplication_not_mod_prime a b = admit()

(*If k a ≡ k b (mod n) and k is coprime with n, then a ≡ b (mod n) *)


let lemma_modular_multiplication_p256 a b = admit()



let lemma_mod_sub_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  distributivity_sub_left 0 (b / n) n;
  // (a - b) % n == (a - (b % n) - (b / n) * n) % n
  lemma_mod_plus (a - (b % n)) (-(b / n)) n

let lemma_mod_add_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  // (a + b) % n == (a + (b % n) + (b / n) * n) % n
  lemma_mod_plus (a + (b % n)) (b / n) n

let lemma_log_and1 a b = 
  logand_lemma a b


let lemma_xor_copy_cond a b mask = 
  let fst = logxor a b in 
  let snd = logand mask fst in 
    logand_lemma mask fst;
  let thrd = logxor a snd in    
    logxor_lemma a snd;
    logxor_lemma a b

let lognot_lemma #t a = admit()

let lemma_equality a b = ()

let neq_mask_lemma #t a b = admit()


let cmovznz4_lemma cin x y = 
  let x2 = neq_mask cin (u64 0) in 
      neq_mask_lemma cin (u64 0);
  let x3 = logor (logand y x2) (logand x (lognot x2)) in
  let ln = lognot (neq_mask cin (u64 0)) in 
    log_and y x2; 
    log_not_lemma x2;
    log_and x ln;
    log_or (logand y x2) (logand x (lognot (x2)))


  
let lemma_equ_felem a b c d  a1 b1 c1 d1  = 
  assert(a = a1 + b1 * pow2 64 + c1 * pow2 128 + d1 * pow2 192 -  b * pow2 64 - c * pow2 128 - d * pow2 192);
  assert(a == a1);
  assert(b == b1);
  assert(c == c1);
  assert(d == d1)



let lemma_eq_funct a b = 
  let a_seq = felem_seq_as_nat a in 
  let b_seq = felem_seq_as_nat b in 

  
  let a0 = Lib.Sequence.index a 0 in 
  let a1 =  Lib.Sequence.index a 1 in 
  let a2 =  Lib.Sequence.index  a 2 in 
  let a3 =  Lib.Sequence.index a 3 in 

  let b0 = Lib.Sequence.index b 0 in 
  let b1 = Lib.Sequence.index b 1 in 
  let b2 = Lib.Sequence.index b 2 in 
  let b3 = Lib.Sequence.index b 3 in 

  assert(uint_v a0 < pow2 64);
  assert(uint_v b0 < pow2 64);
  
  assert(uint_v a0 < pow2 64);
  assert(uint_v b0 < pow2 64);

  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  
  assert(
  uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 128 + uint_v a3 * pow2 192 == 
  uint_v b0 + uint_v b1 * pow2 64 + uint_v b2 * pow2 128 + uint_v b3 * pow2 192);

  lemma_equ_felem (uint_v a0) (uint_v a1) (uint_v a2) (uint_v a3) (uint_v b0) (uint_v b1) (uint_v b2) (uint_v b3);

  assert(Lib.Sequence.index a 0 == Lib.Sequence.index b 0);
  assert(Lib.Sequence.index a 1 == Lib.Sequence.index b 1);
  assert(Lib.Sequence.index a 2 == Lib.Sequence.index b 2);
  assert(Lib.Sequence.index a 3 == Lib.Sequence.index b 3);  

  assert(Lib.Sequence.equal a b)

