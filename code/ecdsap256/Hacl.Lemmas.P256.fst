module Hacl.Lemmas.P256

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul

open Hacl.Spec.P256.Definition
open Spec.P256
open Spec.ECDSA.Lemmas

open FStar.Math.Lemmas
open FStar.Math.Lib

open Lib.Buffer
open FStar.HyperStack.All
open FStar.HyperStack

open FStar.Tactics 
open FStar.Tactics.Canon 

open Spec.P256

#set-options " --z3rlimit 200" 

val lemma_scalar_ith: sc:lbytes 32 -> k:nat{k < 32} -> Lemma
  (v sc.[k] == nat_from_intseq_le sc / pow2 (8 * k) % pow2 8)

let lemma_scalar_ith sc k =
  index_nat_to_intseq_le #U8 #SEC 32 (nat_from_intseq_le sc) k;
  nat_from_intseq_le_inj sc (nat_to_intseq_le 32 (nat_from_intseq_le sc))


val lemma_equ_felem: a: nat {a < pow2 64} 
  -> b: nat {b < pow2 64} 
  -> c: nat {c < pow2 64} 
  -> d: nat {d < pow2 64} 
  -> a1: nat {a1 < pow2 64} 
  -> b1: nat {b1 < pow2 64} 
  -> c1: nat {c1 < pow2 64} 
  -> d1: nat {d1 < pow2 64} -> 
  Lemma 
    (requires (
      a + b * pow2 64 + c * pow2 64 * pow2 64 + d *  pow2 64 * pow2 64 * pow2 64 == 
      a1 + b1 * pow2 64 + c1 * pow2 64 * pow2 64  + d1 *  pow2 64 * pow2 64 * pow2 64))
    (ensures (a == a1 /\ b == b1 /\ c == c1 /\ d == d1))

let lemma_equ_felem a b c d  a1 b1 c1 d1  = 
  assert(a = a1 + b1 * pow2 64 + c1 * pow2 128 + d1 * pow2 192 -  b * pow2 64 - c * pow2 128 - d * pow2 192);
  assert(a == a1);
  assert(b == b1);
  assert(c == c1);
  assert(d == d1)

val lemma_equality: a: felem4 -> b: felem4 -> Lemma (
  let (a_0, a_1, a_2, a_3) = a in 
  let (b_0, b_1, b_2, b_3) = b in 
  if  (uint_v a_0 = uint_v b_0 && uint_v a_1 = uint_v b_1 && uint_v a_2 = uint_v b_2 && uint_v a_3 = uint_v b_3) 
  then as_nat4 a == as_nat4 b else as_nat4 a <> as_nat4 b)

let lemma_equality a b = ()


val lemma_eq_funct: a: felem_seq -> b: felem_seq -> Lemma
   (requires (felem_seq_as_nat a == felem_seq_as_nat b))
   (ensures (a == b))

let lemma_eq_funct a b = 
  let a0 = Lib.Sequence.index a 0 in 
  let a1 = Lib.Sequence.index a 1 in 
  let a2 = Lib.Sequence.index a 2 in 
  let a3 = Lib.Sequence.index a 3 in 

  let b0 = Lib.Sequence.index b 0 in 
  let b1 = Lib.Sequence.index b 1 in 
  let b2 = Lib.Sequence.index b 2 in 
  let b3 = Lib.Sequence.index b 3 in 

  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);

  lemma_equ_felem (uint_v a0) (uint_v a1) (uint_v a2) (uint_v a3) (uint_v b0) (uint_v b1) (uint_v b2) (uint_v b3);
  
  assert(Lib.Sequence.equal a b)


val lemma_eq_funct_: a: felem_seq -> b: felem_seq -> Lemma
   (if felem_seq_as_nat a = felem_seq_as_nat b then a == b else True)

let lemma_eq_funct_ a b = 
  if felem_seq_as_nat a = felem_seq_as_nat b then 
    lemma_eq_funct a b 


val lemma_core_0: a:lbuffer uint64 (size 4) -> h:mem
  -> Lemma (nat_from_intseq_le (as_seq h a) == as_nat h a)

let lemma_core_0 a h = 
  let k = as_seq h a in 
  let z = nat_from_intseq_le k in 
    nat_from_intseq_le_slice_lemma k 1;
    nat_from_intseq_le_lemma0 (Seq.slice k 0 1);
  let k1 = Seq.slice k 1 4 in 
    nat_from_intseq_le_slice_lemma #_ #_ #3 k1 1;
    nat_from_intseq_le_lemma0 (Seq.slice k1 0 1);
  let k2 = Seq.slice k1 1 3 in 
    nat_from_intseq_le_slice_lemma #_ #_ #2 k2 1;
    nat_from_intseq_le_lemma0 (Seq.slice k2 0 1);
    nat_from_intseq_le_lemma0 (Seq.slice k2 1 2)

(*
val lemma_core_1: a:lbuffer uint64 (size 4) -> h:mem ->
  Lemma (nat_from_bytes_le (uints_to_bytes_le (as_seq h a)) == as_nat h a)


let lemma_core_1 a h= 
  lemma_core_0 a h;
  lemma_nat_from_to_intseq_le_preserves_value #U64 #SEC 4 (as_seq h a);
  let n = nat_from_intseq_le (as_seq h a) in 
  uints_to_bytes_le_nat_lemma #U64 #SEC 4 n;
  lemma_nat_to_from_bytes_le_preserves_value #SEC (uints_to_bytes_le #U64 #SEC #4 (as_seq h a)) 32 (as_nat h a)
*)


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


let mul_lemma_1 (a: nat) (c: nat) (b: pos) : Lemma (requires (a < c)) (ensures (a * b < c * b)) = ()

let mul_lemma_ (a: nat) (b: nat) (c: nat) : Lemma (requires (a < c /\ b < c)) (ensures (a * b < c * c)) = ()

let mul_lemma_2 (a: nat) (c: nat) (b: pos) : Lemma (requires (a <= c)) (ensures (a * b <= c * b)) = ()

let mul_lemma_3 (a: nat) (c: nat) (b: nat) (d: nat) : Lemma (requires (a < c && b < d)) (ensures (a * b < c * d)) = ()

let mul_lemma_4 (a: nat) (b: nat) (c: nat) (d: nat) : Lemma (requires (a <= c && b <= d)) (ensures (a * b <= c * d)) = ()


val lemma_low_level0: o0: nat -> o1: nat -> o2: nat -> o3: nat -> f0: nat  ->  f1: nat -> f2: nat -> 
  f3: nat {f0 + f1 * pow2 64 + f2 * pow2 128  + f3 * pow2 192 < pow2 256} -> 
  u: nat {u < pow2 64} -> h2: nat -> c1: nat -> c2: nat -> c3: nat -> h3: nat -> h4: nat ->
  Lemma
  (requires (
    h2 * pow2 64 * pow2 64 +  o0 + o1 * pow2 64 + c1 * pow2 64 * pow2 64 ==  f0 * u + f1 * u * pow2 64 /\
    o2 + c2 * pow2 64 + h3 * pow2 64 - h2 - c1 == f2 * u /\
    o3 + c3 * pow2 64 + h4 * pow2 64 - h3 - c2 == f3 * u)
  )
  (ensures 
    (o0 + o1 * pow2 64 + o2 * pow2 128 +  o3 * pow2 192 + (c3 + h4) * pow2 256  == (f0  + f1 * pow2 64 + f2  * pow2 128  + f3 * pow2 192) * u /\
    f0 * u + f1 * u * pow2 64 + f2 * u * pow2 128  + f3 * u * pow2 192 < pow2 320 /\
    (c3 + h4) < pow2 64)
  )

let lemma_low_level0 o0 o1 o2 o3 f0 f1 f2 f3 u h2 c1 c2 c3 h3 h4 = 
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);  
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 320); 

  mul_lemma_3  (f0 + f1 * pow2 64 + f2 * pow2 128 + f3 * pow2 192) (pow2 256) u (pow2 64)


val log_and: a: uint64 -> b: uint64{uint_v b == 0 \/ uint_v b == pow2 64 - 1} ->
  Lemma (if uint_v b = 0 then uint_v (logand a b) == 0 else uint_v (logand a b) == uint_v a)

let log_and a b = 
  logand_lemma b a;
  logand_spec a b;
  logand_spec b a;
  UInt.logand_commutative #(bits U64) (v a) (v b)


val logor_commutative: a: uint64 -> b: uint64 -> Lemma (logor a b == logor b a)

let logor_commutative a b = 
  logor_spec a b;
  logor_spec b a;
  UInt.logor_commutative #(bits U64) (v a) (v b)


val log_or: a: uint64 -> b: uint64 {uint_v b == 0 \/ uint_v a == 0} -> Lemma (
  if uint_v b = 0 then uint_v (logor a b) == uint_v a else uint_v (logor a b) == uint_v b)

let log_or a b = 
    if uint_v b = 0 then 
       begin
	 logor_lemma b a;
	 logor_commutative a b
       end
    else 
      begin
	assert(uint_v a == 0);
	logor_lemma a b
      end


val cmovznz4_lemma: cin: uint64 -> x: uint64 -> y: uint64 -> Lemma (
  let mask = neq_mask cin (u64 0) in 
  let r = logor (logand y mask) (logand x (lognot mask)) in 
  if uint_v cin = 0 then uint_v r == uint_v x else uint_v r == uint_v y)

let cmovznz4_lemma cin x y = 
  let x2 = neq_mask cin (u64 0) in 
      neq_mask_lemma cin (u64 0);
  let x3 = logor (logand y x2) (logand x (lognot x2)) in
  let ln = lognot (neq_mask cin (u64 0)) in 
    log_and y x2; 
    lognot_lemma x2;
    log_and x ln;
    log_or (logand y x2) (logand x (lognot x2))


val lemma_xor_copy_cond: a: uint64 -> b: uint64 -> mask: uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 -1} -> Lemma(
  let r = logxor a (logand mask (logxor a b)) in 
  if uint_v mask = pow2 64 - 1 then r == b else r == a)

let lemma_xor_copy_cond a b mask = 
  let fst = logxor a b in 
  let snd = logand mask fst in 
    logand_lemma mask fst;
  let thrd = logxor a snd in    
    logxor_lemma a snd;
    logxor_lemma a b

val power_one: a: nat -> Lemma (pow 1 a == 1) 

let rec power_one a = 
  match a with 
  | 0 -> assert_norm (pow 1 0 == 1)
  | _ -> power_one (a - 1) 


noextract
val pow_plus: a: nat -> b: nat -> c: nat -> 
  Lemma (ensures (pow a b * pow a c = pow a (b + c))) 
  (decreases b)

let rec pow_plus a b c = 
  match b with 
  | 0 -> assert_norm (pow a 0 = 1)
  | _ -> pow_plus a (b - 1) c


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


val power_distributivity_2: a: nat -> b: nat -> c: pos -> Lemma (pow (a * b) c == pow a c * pow b c)

let rec power_distributivity_2 a b c = 
  match c with 
  |0 -> ()
  |1 -> ()
  | _ -> 
    calc (==)
    {
      pow (a * b) c;
      (==) {assert_by_tactic (pow (a * b) c == pow (a * b) (c - 1) * a * b) canon}
      pow (a * b) (c - 1) * a * b;
      (==) {power_distributivity_2 a b (c - 1)}
      pow a (c - 1) * pow b (c - 1) * a * b;
      (==) {assert_by_tactic (pow a (c - 1) * pow b (c - 1) * a * b == pow a c * pow b c) canon}
      pow a c * pow b c;
    }


noextract
val power_mult: a: nat -> b: nat -> c: nat -> Lemma (pow (pow a b) c == pow a (b * c))

let rec power_mult a b c = 
  match c with 
  |0 -> ()
  |_ ->  power_mult a b (c - 1); 
    pow_plus a (b * (c - 1)) b


(* Start of Marina RSA PSS code *)
val lemma_fpow_unfold0: a: nat -> b: pos {1 < b /\ b % 2 = 0} -> prime: pos {a < prime} -> Lemma (
  exp #prime a b = exp #prime (fmul a a) (b / 2))

let lemma_fpow_unfold0 a b prime = ()


val lemma_fpow_unfold1: a: nat -> b: pos {1 < b /\ b % 2 = 1} -> prime: pos { a < prime} -> Lemma (
  exp #prime a b = fmul (exp #prime (fmul a a) (b / 2)) a)

let lemma_fpow_unfold1 a b prime = ()


val lemma_pow_unfold: a: nat -> b: pos -> Lemma (a * pow a (b - 1) == pow a b)
let lemma_pow_unfold a b = ()


val lemma_mul_associativity_3: a: nat -> b: nat -> c: nat -> Lemma (a * b * c == a * c * b)
let lemma_mul_associativity_3 a b c = ()


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

(*
val lemma_decrease_pow: a: nat -> Lemma (
  (a * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64)) % prime256 == 
  (a * modp_inv2 (pow2 256)) % prime256) 

let lemma_decrease_pow a = 
  assert_norm(modp_inv2 (pow2 64) = 6277101733925179126845168871924920046849447032244165148672);
  assert_norm(modp_inv2 (pow2 256) = 115792089183396302114378112356516095823261736990586219612555396166510339686400 );
  assert_norm((modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2(pow2 64)) % prime256  = (modp_inv2 (pow2 256)) % prime256);
  lemma_mod_mul_distr_r a (modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2(pow2 64)) prime256;
  lemma_mod_mul_distr_r a (modp_inv2 (pow2 256)) prime256
*)

val lemma_brackets : a: int -> b: int -> c: int -> Lemma (a * b * c = a * (b * c))

let lemma_brackets a b c = ()

val lemma_brackets4 : a: int -> b: int -> c: int -> d: nat -> Lemma (a * b * c * d = a * (b * c * d))

let lemma_brackets4 a b c d = ()

val lemma_brackets5_0 : a: int -> b: int -> c: int -> d: nat ->e: nat ->  Lemma (a * b * c * d * e = a * (b * c * d * e))

let lemma_brackets5_0 a b c d e= ()


val lemma_twice_brackets: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> h: int-> Lemma (
  (a * b * c) * (d * e * f) * h = a * b * c * d * e * f * h)

let lemma_twice_brackets a b c d e f h = ()


val lemma_mul_nat2: a: nat -> b: nat -> Lemma (a * b >= 0)

let lemma_mul_nat2 a b = ()


val lemma_mul_nat: a:nat -> b:nat -> c: nat -> Lemma (a * b * c >= 0)

let lemma_mul_nat a b c = ()


val lemma_mul_nat4: a:nat -> b:nat -> c: nat -> d: nat -> Lemma (a * b * c * d >= 0)

let lemma_mul_nat4 a b c d = ()


val lemma_mul_nat5: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (a * b * c * d * e >= 0)

let lemma_mul_nat5 a b c d e = ()


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
