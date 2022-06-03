module Hacl.EC.Lemmas

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul

open FStar.Tactics 
open FStar.Tactics.Canon 

open Hacl.Spec.EC.Definition
open Spec.ECC.Curves
open Spec.ECDSA.Lemmas

open FStar.Math.Lemmas

open Spec.ECC

#set-options " --z3rlimit 200" 

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
  

val logand_lemma: a: uint64 -> b: uint64{uint_v b == 0 \/ uint_v b == pow2 64 - 1} ->
  Lemma (if uint_v b = 0 then uint_v (logand a b) == 0 else uint_v (logand a b) == uint_v a)

let logand_lemma a b = 
  logand_lemma b a;
  logand_spec a b;
  logand_spec b a;
  UInt.logand_commutative #(bits U64) (v a) (v b)

val logor_commutative: a: uint64 -> b: uint64 -> Lemma (logor a b == logor b a)

let logor_commutative a b = 
  logor_spec a b;
  logor_spec b a;
  UInt.logor_commutative #(bits U64) (v a) (v b)

val logor_lemma_one_element_is_zero: a: uint64 -> b: uint64 {uint_v b == 0 \/ uint_v a == 0} -> 
  Lemma (if uint_v b = 0 then uint_v (logor a b) == uint_v a else uint_v (logor a b) == uint_v b)

let logor_lemma_one_element_is_zero a b = 
  if uint_v b = 0 then 
    begin
      logor_lemma b a;
      logor_commutative a b
    end
  else 
    logor_lemma a b


val cmovznz4_lemma: cin: uint64 -> x: uint64 -> y: uint64 -> Lemma (
  let mask = neq_mask cin (u64 0) in 
  let r = logor (logand y mask) (logand x (lognot mask)) in 
  if uint_v cin = 0 then uint_v r == uint_v x else uint_v r == uint_v y)

let cmovznz4_lemma cin x y = 
  let x2 = neq_mask cin (u64 0) in 
      neq_mask_lemma cin (u64 0);
  let x3 = logor (logand y x2) (logand x (lognot x2)) in
  let ln = lognot (neq_mask cin (u64 0)) in 
  logand_lemma y x2; 
  lognot_lemma x2;
  logand_lemma x ln;
  logor_lemma_one_element_is_zero (logand y x2) (logand x (lognot x2))

val lemma_xor_copy_cond: #t:inttype{unsigned t} -> #l:secrecy_level -> a: uint_t t l -> b: uint_t t l 
  -> mask: uint_t t l {uint_v mask = 0 \/ uint_v mask = maxint t} -> Lemma(
  let r = logxor a (logand mask (logxor a b)) in 
  if uint_v mask =  maxint t then r == b else r == a)

let lemma_xor_copy_cond a b mask = 
  let fst = logxor a b in 
  let snd = logand mask fst in 
    logxor_lemma a b;
    Lib.IntTypes.logand_lemma mask fst; 
  let thrd = logxor a snd in    
    logxor_lemma a snd


val power_zero: a: nat -> Lemma (pow a 0 == 1)

let power_zero a = ()


val power_one: a: nat -> Lemma (pow 1 a == 1) 

let rec power_one a = 
  match a with 
  | 0 -> assert_norm (pow 1 0 == 1)
  | _ -> power_one (a - 1) 


val power_one_2: a: nat -> Lemma (pow a 1 == a) 

let power_one_2 a = ()


val pow_plus: a: nat -> b: nat -> c: nat -> 
  Lemma (ensures (pow a b * pow a c = pow a (b + c))) 
  (decreases b)

let rec pow_plus a b c = 
  match b with 
  | 0 -> assert_norm (pow a 0 = 1)
  | _ -> pow_plus a (b - 1) c


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


val power_mult: a: nat -> b: nat -> c: nat -> Lemma (pow (pow a b) c == pow a (b * c))

let rec power_mult a b c = 
  match c with 
  |0 -> ()
  |_ ->  power_mult a b (c - 1); 
    pow_plus a (b * (c - 1)) b


(* Start of Marina RSA PSS code *)
val lemma_fpow_unfold0: a: nat -> b: pos {1 < b /\ b % 2 = 0} -> prime: pos {a < prime} -> Lemma (
  exp #prime a b = exp #prime (fmul #prime a a) (b / 2))

let lemma_fpow_unfold0 a b prime = ()


val lemma_fpow_unfold1: a: nat -> b: pos {1 < b /\ b % 2 = 1} -> prime: pos { a < prime} -> Lemma (
  exp #prime a b = fmul #prime (exp #prime (fmul #prime a a) (b / 2)) a)

let lemma_fpow_unfold1 a b prime = ()


val lemma_pow_unfold: a: nat -> b: pos -> Lemma (a * pow a (b - 1) == pow a b)
let lemma_pow_unfold a b = ()


(* val lemma_mul_associativity_3: a: nat -> b: nat -> c: nat -> Lemma (a * b * c == a * c * b)
let lemma_mul_associativity_3 a b c = ()
 *)

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
	fmul #n a (exp #n (fmul #n a a) (b / 2));
	(==) { lemma_pow_mod_n_is_fpow n (fmul #n a a) (b / 2) }
	fmul #n a (pow (fmul #n a a) (b / 2) % n);
	(==) { power_distributivity (a * a) (b / 2) n }
	fmul #n a (pow (a * a) (b / 2) % n);
	(==) { lemma_pow_double a (b / 2) }
	fmul #n a (pow a (b / 2 * 2) % n);
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

val lemma_multiplication_associative : a: int -> b: int -> c: int -> Lemma (a * b * c = a * (b * c))

let lemma_multiplication_associative a b c = ()


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
